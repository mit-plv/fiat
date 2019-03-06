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
 */

#ifndef LANDSHARKPAINTBALL_H
#define LANDSHARKPAINTBALL_H

#include <string>
#include <vector>

#include <boost/thread.hpp>
#include <boost/thread/mutex.hpp>
#include <boost/date_time/posix_time/posix_time.hpp>

#include RADL_HEADER

/**
 * This enum describes the different control mode.
 */
enum PaintballControlMode
{
  IDLE,
  SINGLE_SHOT,
  TRIPLE_SHOT,
  BURST
};

/**
 * This class provides an interface to control the paintball on the Landshark.
 */
class LandsharkPaintball
{
  public:
    /**
     * Constructor
     */
    LandsharkPaintball();

    /**
     * Destructor
     */
    ~LandsharkPaintball();

    int step( const radl_in_t *in, const radl_in_flags_t *in_flags, radl_out_t *out, radl_out_flags_t *out_flags );

    /**
     * Initialize the communication with the interface
     * @param rIpAddress IP address of the paintball controller
     * @throw std::runtime_error thrown when unable to initialize the communication with the controller
     */
    void Initialize(const std::string& rIpAddress);

    /**
     * Shoot with the paintball
     */
    void Shoot();

    /**
     * Shoot three times with the painball
     */
    void TripleShoot();

    /**
     * Use the paintball in burst mode
     */
    void Burst();

  private:
    void CommunicationProcess();
    void ShotControl(char command);

    boost::thread_group m_ThreadGroup;
    unsigned int volatile m_DesiredProcessPeriod_us; // in us
    //unsigned int volatile m_ControllerUpdateRate;
    int volatile m_SocketFileDescriptor;
    bool m_IsCommunicationRunning;
    boost::mutex m_RunningMutex;
    std::string m_ControllerIp;
    int m_ControllerPort;

    inline void SetRunning( const bool value )
    {
      boost::mutex::scoped_lock lock( m_RunningMutex );
      m_IsCommunicationRunning = value;
    }

    inline bool GetRunning( )
    {
      boost::mutex::scoped_lock lock( m_RunningMutex );
      return m_IsCommunicationRunning;
    }

    boost::mutex m_ControlMutex;
    PaintballControlMode volatile m_ControlMode;
};

#endif
