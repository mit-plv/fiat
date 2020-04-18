#!/bin/sh

echo "Starting ROS test." >/tmp/rostst.log
echo >>/tmp/rostst.log

for N in `ls *.txt | sort -n`
do
    echo >>/tmp/rostst.log
    echo "=== TEST $N ===" >>/tmp/rostst.log
    echo >>/tmp/rostst.log

    nc localhost 11311 <$N >>/tmp/rostst.log

    echo >>/tmp/rostst.log
done
