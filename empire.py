#!/usr/bin/env python
"""Main initialization file for empire client."""

#    Copyright (C) 1998-1999 Kevin O'Connor
#    Copyright (C) 2013 William Fittge
#
#    This program is free software; you can redistribute it and/or modify
#    it under the terms of the GNU General Public License as published by
#    the Free Software Foundation; either version 2 of the License, or
#    (at your option) any later version.
#
#    This program is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#    GNU General Public License for more details.
#
#    You should have received a copy of the GNU General Public License
#    along with this program; if not, write to the Free Software
#    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

import sys
import os
import getopt
import string
import operator
import traceback

# Key Ideas:

# What is contained within this file:

# This file contains the code necessary to "bootstrap" the other code
# files.  The code in this file has been left intentionally sparse because
# it is often translated to byte-code multiple times.


# The use of global variables throughout this project:

# In general, I dislike the use of global variables.  I have made an effort
# to document each use of global variables in each module.  (True global
# variables - not global constants.)  There are a couple of critical global
# variables that future developers should know of:
#
# viewer : The viewer class is defined in just about all modules.  This
# variable is used for reporting errors, sending commands, and many other
# functions.
#
# empDb.megaDB : This is the location of the internal database.  This
# database stores all the gathered information from the server.  Different
# databases can be dynamicaly loaded/saved to disk, but at any one time
# the client only supports a single countries' database.
#
# Although I dislike global variables, I felt it necessary to use them in
# the above circumstances.  Under normal conditions, almost all classes and
# functions require both viewer and megaDB.  It makes little sense to pass
# these variables with nearly every single call.  Also, that many
# references to the same variable is bound to cause some form of circular
# referencing, which is not a good idea(tm) in Python.


###########################################################################
############################ Python 1.5.2 Check ###########################

try:
    test = r"Test for 'r' string flag."
    del test

    try:
        # Python 1.5.1 and earlier returned 0 for atoi('-')...
        string.atoi('-')
    except ValueError:
        pass
    else:
        raise "outdated.."
except:
    print """

It appears this version of Python is out-dated.  You must have Python 1.5.2
or later installed in order for the client to work.  See the web site at:
http://www.python.org/ for more information on upgrading Python.

"""
    sys.exit(1)

VERSION = '2.00.0'

###########################################################################
#############################  Initialization  ############################

def initialize():
    """Parse the command-line and initialize the socket and interface."""
    global viewer

    # Attempt to find the username.
    try: USERNAME = os.environ['USER']
    except (AttributeError, KeyError):
        USERNAME = 'PythonTk'

    # Check command line for the database filename.
    usage = ("Usage:\n"
             + str(sys.argv[0]) + " [-a] [-v] [-l] [-p] [-t|-c|-x] [-n] [-I <include directory>] "
             +"[<database filename>]")
    versionText = """Python/Tk Empire Interface (PTkEI) %s
Copyright (C) 1998-2013 Kevin O'Connor and others.
PTkEI comes with ABSOLUTELY NO WARRANTY; for details
type `%s -l'.  This is free software, and you are welcome
to redistribute it under certain conditions; type `%s -l'
for details.""" % (VERSION, str(sys.argv[0]), str(sys.argv[0]))

    licenseText = """Python/Tk Empire Interface (PTkEI) %s
Copyright (C) 1998-2000 Kevin O'Connor.
Copyright (C) 2001-2002 Laurent Martin.
Copyright (C) 2013 William Fittge.

    This program is free software; you can redistribute it and/or
    modify it under the terms of the GNU General Public License
    version 2 as published by the Free Software Foundation.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
    General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111,
    USA.

To contact the developers, please send email to <ptkei2@gmail.com>.
""" % (VERSION)


    try:
        opts, args = getopt.getopt(sys.argv[1:], 'apvltcxnh?I:', ['help'])
    except getopt.error:
        print usage
        sys.exit()
    # Check for help request
    argnames = map(operator.getitem, opts, [0]*len(opts))
    if ('-h' in argnames or '-?' in argnames or '--help' in argnames
        or len(args) > 1):
        print usage
        sys.exit()
    if '-v' in argnames:
        print versionText
        sys.exit(0)
    if '-l' in argnames:
        print licenseText
        sys.exit(0)
    # Check for visual assistance
    if '-a' in argnames:
        assist = 1
    else:
        assist = 0
    # Check for predict flag
    if '-p' in argnames:
        predict = 1
    else:
        predict = 0
    # Check for forced text startup
    if '-t' in argnames:
        textonly = 1
    elif '-c' in argnames:
        textonly = 2
    elif '-x' in argnames:
        textonly = -1
    else:
        textonly = 0
    # Check for a request to not automatically connect.
    autoconnect = ('-n' not in argnames)
    # Get the database name
    if len(args) == 1:
        FILE = args[0]
    else:
        FILE = "EmpDB"
    # Check for included directory list
    # The default include path is: the current directory, the program's
    # directory.
    includes = ['', sys.path[0]]
    for i, j in opts:
        if i == '-I':
            includes[:0] = [j]

    def pathPrefix(str, dirlist=includes):
        """Check installation directory for file."""
        for i in dirlist:
            fullname = os.path.join(i, str)
            if os.path.isfile(fullname):
                return fullname
        # Couldn't find the file - maybe the caller will have more luck:
        return ""

    # Mangle the system module path.  Replace current directory with src/
    # sub-directory.
    sys.path[0] = os.path.join(sys.path[0], "src")

    # Load modules
    import empDb
    import empQueue
    import empCmd

    # Hack!  Pass on the pathPrefix function
    empQueue.pathPrefix = pathPrefix

    # Load the database.
    try:
        empDb.DBIO.load(FILE)
    except:
        print ("PTkEI: Encountered error while loading database.\n"
               "PTkEI: Perhaps this is an old database?\n")
        traceback.print_exc()
        sys.exit()
    # Setup an automatic database saver.
    sys.exitfunc = empDb.DBIO.save

    empDb.predict = predict
    empDb.assist = assist
    if textonly == 1:
        import empText
        viewer = empText.SText()
    elif textonly == 2:
        import empCurses
        viewer = empCurses.Curses()
    elif textonly == -1:
        import empTk
        viewer = empTk.mainWin()
    else:
        # Attempt to load Tk viewer.  If that fails use text interface.
        try:
            import empTk
        except:
            print (
                'An exception (%s) raised during Tk initialization:\n"%s"\n'
                "Reverting to text interface.\n"
                ) % tuple(sys.exc_info()[:2])
            import empText
            viewer = empText.SText()
        else:
            viewer = empTk.mainWin()

    # Set some common defaults among all the interfaces.
    empDb.viewer = empCmd.viewer = empQueue.viewer = viewer

    # Set everything up
    sockQueue = empQueue.EmpData(USERNAME)
    cmdParser = empCmd.EmpParse(sockQueue)
    viewer.ioq = cmdParser

    # Force connect
    if autoconnect:
        sockQueue.loginParser.Connect()

###########################################################################
#############################  Startup        #############################

if __name__=='__main__':
    # This file is being run as the main process.
    initialize()

##      # Pmw hack
##      sys.path[:0] = ['/scratch/koconnor', '/usr/src']

    # Go!
    viewer.main()
