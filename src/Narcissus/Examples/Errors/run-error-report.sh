#!/usr/bin/env bash

# This script runs various Narcissus error cases and collects the Narcissus
# output into a report file.

# Configuration.
examples_dir="src/Narcissus/Examples/Errors"
coqc_args="-R src Fiat -R Bedrock Bedrock -I src/Common/Tactics"
time_limit="10s"
output_file="error-report.txt"

# Write a header to the output file.
echo "--------------------------------------------" >  $output_file
echo "-- Narcissus Error Examples Output Report --" >> $output_file
echo "--------------------------------------------" >> $output_file
echo "" >> $output_file

# Iterate through all .v files in the examples_dir.
echo "Looking for examples in $examples_dir."
for errfile in $(find $examples_dir -name '*.v')
do
  echo -n "$errfile... "
  echo "$errfile" >> $output_file
  echo "---------------------------------------------" >> $output_file
  start=$(($(date +%s%N)/1000000))
  timeout -v --foreground $time_limit coqc $coqc_args $errfile >> $output_file 2>&1
  end=$(($(date +%s%N)/1000000))
  echo "($((end-start)) ms)"

  # Place exactly one empty line at end of file.
  stripped_newlines=$(<$output_file)
  printf '%s\n\n' "$stripped_newlines" > $output_file
done

# Strip extra newlines from output file.
stripped_newlines=$(<$output_file)
printf '%s\n' "$stripped_newlines" > $output_file
