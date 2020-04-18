#!/usr/bin/python
import sys, os
import shutil
import re
import os.path

def uncomment(tkn, data):
    return re.sub(r"\(\*%s(([^*]|(\*[^)]))+)\*\)" % tkn, r"\1", data)

def process_file(src, trg):
    data = open('%s.v' % src,'r').read()

    if not os.path.exists(os.path.dirname(trg)):
        os.makedirs(os.path.dirname(trg))

    if '(*TIME' in data:
        f = open('%s.v' % trg, 'w')
        f.write(uncomment("TIME", data))
        f.close()
    else:
        for ext in ['v','v.d','vo','glob']:
            try:
                shutil.copyfile('%s.%s' % (src,ext), '%s.%s' % (trg,ext))
                stat = os.stat('%s.%s' % (src,ext))
                os.utime('%s.%s' % (trg,ext), (stat.st_atime, stat.st_mtime))
            except:
                pass

def main(temp_dir, files):
    for f in files:
        assert f.endswith('.v')
        process_file(f[:-2], os.path.join(temp_dir, f[:-2]))

# timer.py [temp_dir] [files+]
if __name__ == '__main__':
    assert len(sys.argv) > 2

    main(sys.argv[1], sys.argv[2:])
