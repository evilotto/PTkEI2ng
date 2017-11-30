#! /usr/bin/python

# This script converts a PTkEI database from the format used by PTkEI
# versions 1.12 and 1.13.3 to the format used by PTkEI 1.14.0.

import sys
import os
import cPickle

sys.path[0] = os.path.join(sys.path[0], "../src")

import empDb

if len(sys.argv) == 1:
    new = 'EmpDB'
    old = 'EmpDB.old'
elif len(sys.argv) == 2:
    new = sys.argv[1]
    old = new + '.old'
else:
    print
    """
Wrong number of arguments
Usage: updateDB.py [dbfile]
    """
try:
    f = open(new, 'r')
except IOError, e:
    print new, ':', e.strerror
    sys.exit(1)
    
try:
    db = cPickle.load(f)
except cPickle.UnpicklingError:
    print "File", new, "isn't a valid PTkEI database."
    sys.exit(1)
f.close()

try: 
    os.rename(new, old) 
except OSError, e: 
    print new, ':', e.strerror 
    sys.exit(1) 


if db['DB_Version'] < 32.3:
    print 'Updating file', new
    db['sectortype'] = {' ': {}}
    db['DB_Version'] = 32.3
else:
    print 'Nothing to be done for file', new

f = open(new, 'w')
cPickle.dump(db,f)
f.close()

