/*
 * Copyright (C) 2012, SRI International (R)
 *
 * The material contained in this release is copyrighted. It may not be copied,
 * reproduced, translated, reverse engineered, modified or reduced to any electronic
 * medium or machine-readable form without the prior written consent of
 * SRI International (R).
 *
 * Portions of files in this release may be unpublished work
 * containing SRI International (R) CONFIDENTIAL AND PROPRIETARY INFORMATION.
 * Disclosure, use, reverse engineering, modification, or reproduction without
 * written authorization of SRI International (R) is likewise prohibited.
 *
 * Author(s): Thomas de Candia (thomasd@ai.sri.com)
 *
 * $Id$
 */

#include "LandsharkPaintball.h"

#include <sstream>
#include <exception>

extern "C"
{
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <strings.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <errno.h>
#include <arpa/inet.h>
}

// Command parameter
static const std::string COMMAND_HEAD = "9;1;";
static const std::string COMMAND_TAIL = ";";
// Time and period constants
//static const unsigned int PAINTBALL_UPDATE_RATE = 5;
// Socket communication parameters
static const int UNDEFINED_SOCKET_FILE_DESCRIPTOR = -1;
static const int DEFAULT_PROTOCOL = 0;
static const int BUFFER_SIZE = 256;
static const int REUSEADDR_OPTVAL = 1;

LandsharkPaintball::LandsharkPaintball()
  : m_DesiredProcessPeriod_us(1e5)
  , m_ControlMode(IDLE)
  , m_SocketFileDescriptor(UNDEFINED_SOCKET_FILE_DESCRIPTOR)
  , m_IsCommunicationRunning(false)
  , m_ControllerIp( "192.168.15.78" )
  , m_ControllerPort( 23 )
{
  m_ControllerIp = *RADL_THIS->ip_address;
  m_ControllerPort = *RADL_THIS->ip_port;

  std::cout << "[paintball] device IP: " << m_ControllerIp;
  std::cout << ", port: " << m_ControllerPort << std::endl;
  this->Initialize(m_ControllerIp);
  SetRunning( true );
  // start communication process thread
  m_ThreadGroup.create_thread(boost::bind(&LandsharkPaintball::CommunicationProcess, this));
}

LandsharkPaintball::~LandsharkPaintball()
{
  SetRunning( false );
  m_ThreadGroup.join_all();
  close(m_SocketFileDescriptor);
}

int LandsharkPaintball::step( const radl_in_t *in, const radl_in_flags_t *in_flags, radl_out_t *out, radl_out_flags_t *out_flags ) {
  uint8_t trigger( in->trigger->data );

  if ( radl_is_failing( in_flags->trigger ) ) {
    std::cerr << "[paintball] RADL failure flags set!" << std::endl;
  }
  else if ( trigger == radlast_constants()->PaintballTrigger->SINGLE_SHOT ) {
    this->Shoot();
  }
  else if ( trigger == radlast_constants()->PaintballTrigger->TRIPLE_SHOT ) {
    this->TripleShoot();
  }
  else if ( trigger == radlast_constants()->PaintballTrigger->BURST_SHOT ) {
    this->Burst();
  }
  else if ( trigger == radlast_constants()->PaintballTrigger->NONE ) {
    // do nothing 
  }
  else {
    std::cerr << "[paintball] unknown mode: trigger= " << (uint8_t) trigger << std::endl;
  }
}

void LandsharkPaintball::Initialize(const std::string& rIpAddress)
{
  if ( GetRunning() ) {
    std::cout << "Process is already initialized, will return." << std::endl;
    return;
  }

  m_SocketFileDescriptor = socket(AF_INET, SOCK_STREAM, DEFAULT_PROTOCOL);
  if (m_SocketFileDescriptor <  0) {
    std::stringstream ss;
    ss  << "Unable to create socket, error: " << strerror(errno);
    throw std::runtime_error(ss.str());
  }

  int result = setsockopt(m_SocketFileDescriptor, SOL_SOCKET, SO_REUSEADDR, &REUSEADDR_OPTVAL, sizeof(REUSEADDR_OPTVAL));
  if (result < 0) {
    std::stringstream ss;
    ss  << "Unable to set socket option SO_REUSEADDR, error: " << strerror(errno);
    throw std::runtime_error(ss.str());
  }

  struct sockaddr_in paintballServerAddress;
  bzero((char *) &paintballServerAddress, sizeof(paintballServerAddress));
  paintballServerAddress.sin_addr.s_addr = inet_addr(rIpAddress.c_str());
  paintballServerAddress.sin_family = AF_INET;
  paintballServerAddress.sin_port = htons( m_ControllerPort );

  result = connect(m_SocketFileDescriptor, (struct sockaddr *) &paintballServerAddress,sizeof(paintballServerAddress));
  if (result < 0) {
    std::stringstream ss;
    ss  << "Unable to connect to socket with address: " << rIpAddress << ", error: " << strerror(errno);
    throw std::runtime_error(ss.str());
  }

  char buffer[BUFFER_SIZE];
  bzero(buffer, BUFFER_SIZE);
  sprintf(buffer, "u;");

  result = write(m_SocketFileDescriptor, buffer, strlen(buffer));
  if (result < 0) {
    std::stringstream ss;
    ss << "Failed to write to socket, error: " << strerror(errno) << std::endl;
    throw std::runtime_error(ss.str());
  }

  bzero(buffer, BUFFER_SIZE);

  usleep(50000);

  result = read(m_SocketFileDescriptor, buffer, BUFFER_SIZE - 1);
  if (result < 0) {
    std::stringstream ss;
    ss << "Failed to read socket, error: " << strerror(errno) << std::endl;
    throw std::runtime_error(ss.str());
  }
  std::cout << "[paintball] Paintball id: " << buffer;

}

void LandsharkPaintball::Shoot()
{
  boost::mutex::scoped_lock lock( m_ControlMutex );
  m_ControlMode = SINGLE_SHOT;
}

void LandsharkPaintball::TripleShoot()
{
  boost::mutex::scoped_lock lock( m_ControlMutex );
  m_ControlMode = TRIPLE_SHOT;
}

void LandsharkPaintball::Burst()
{
  boost::mutex::scoped_lock lock( m_ControlMutex );
  m_ControlMode = BURST;
}

void LandsharkPaintball::CommunicationProcess()
{
  std::cout << "[paintball] starting thread" << std::endl;
  unsigned int loopCount = 0;
  boost::posix_time::time_duration processPeriod;
  boost::posix_time::ptime startTime = boost::posix_time::microsec_clock::local_time();

  while ( GetRunning() )
  {
    processPeriod = boost::posix_time::microsec_clock::local_time() - startTime;

    long timeToSleep = m_DesiredProcessPeriod_us - processPeriod.total_microseconds();
    if (timeToSleep > 0)
    {
      boost::this_thread::sleep(boost::posix_time::microseconds(timeToSleep));
    }

    startTime = boost::posix_time::microsec_clock::local_time();

    //if (loopCount % m_ControllerUpdateRate)
    {
      boost::mutex::scoped_lock lock( m_ControlMutex );
      switch (m_ControlMode)
      {
        case SINGLE_SHOT:
            ShotControl('s');
            break;
        case TRIPLE_SHOT:
            ShotControl('t');
            break;
        case BURST:
            ShotControl('a');
            break;
        case IDLE:
            break;
        default:
            break;
      }
      m_ControlMode = IDLE;
    }

    ++loopCount;
  } // while
  std::cout << "[paintball] stopping thread" << std::endl;
}

void LandsharkPaintball::ShotControl(char command)
{
  if (m_SocketFileDescriptor == UNDEFINED_SOCKET_FILE_DESCRIPTOR)
  {
    std::cerr << "Try to communicate with a socket using an undefined file descriptor." << std::endl;
    return;
  }

  std::stringstream bufferStream;
  bufferStream << COMMAND_HEAD << command << COMMAND_TAIL;
  std::string bufferStr = bufferStream.str();

  int result = write(m_SocketFileDescriptor, bufferStr.c_str(), bufferStr.size());
  if (result < 0)
  {
    std::cerr << "Failed to write to socket, error: " << strerror(errno) << std::endl;
  }
}

