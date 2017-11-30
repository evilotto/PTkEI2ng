"""Routines to manage and store data from a local database."""

# version 1.0.7
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
import signal
import string
import cPickle
import operator
import time
import traceback

# Key Ideas:

# What is contained within this file:

# This file supports all the functions and classes that are necessary to
# import the empire database.  There are three main classes defined within
# this file: dictDB, Countries, and EmpTime.  See the documentation for
# each of these classes for more information on what they do.  This file
# can be used independently from the rest of the program.  To load the
# database, import this module and then call loadDB(name_of_file).


# Global variables:

# megaDB : This is the main data store for the current connection.
#
# DBIO : This is an instance of class DatabaseSaver.  It is used to
# load/save the global database.  (Since it only works on a global
# variable, it may as well be a global variable.)


# Accessing the empire database:

# The empire database is stored in the global variable megaDB.  It is
# generally accessed using empDb.megaDB.  This is a "mega" database - it is
# comprised of a number of sub-databases.  (megaDB is actually a dictionary
# with string keys that correspond to the various data that has been
# accumulated.)  In addition to the land, ship, plane, and sector data that
# is acquired via the dump commands, the megaDB also contains country
# information, telegrams, version data, etc.  (See the resetDB() routine
# for a complete list.)  An example - lets say the designation of a sector
# would like to be accessed - the reference is
# empDb.megaDB['SECTOR'][(x,y)]['des'].  empDb.megaDB refers to the mega
# database.  'SECTOR' is a reference to the sector sub-database.  (For
# historical reasons, those databases that can be dumped via a dump command
# have the same name as the corresponding dump identifier.)  (x,y) is a
# tuple that comprises the key for the sector.  'des' is for the
# designation.  (For those databases that have a corresponding dump, the
# variable names are from the dump header.  For databases that do not have
# a dump, see the resetDB() function.)


# The update database:

# Many of the database helper classes and all of the empire parsers utilize
# the update database that is stored in the global variable updateDB.
# Basically, whenever an _actual_ change is made to the mega database, the
# update database will also reflect that change.  The updateDB and megaDB
# look and behave identically.  The only difference is that megaDB will
# always contain a full set of data while the updateDB frequently only
# contains a small subset of the total data.  (That which has been updated
# recently.)  This feature is used by the Tk graphical interface to detect
# when an actual change to the database occurs, and to redraw where
# appropriate.  It is the responsibility of the interface to periodically
# check for updates.  Also, it is the interface's responsibility to clear
# the updateDB when done.


###########################################################################
#############################  dictDB class   #############################
class dictDB:
    """Store information for server databases.

    This class mimics a standard dictionary type in many ways.  (It defines
    the getitem, get, keys, values, and items methods.)  However, it is
    specifically tailored for the server databases.  (IE. data from a
    dump/pdump/sdump/etc. - the sector and unit databases.)  This tailoring
    is done in two ways.

    First, there is a seamless tracking of secondary indexes.  Any series
    of keys may be used to designate any number of secondary index at the
    creation time of this class.  When an update is made, not only is the
    item inserted into the primary database, but a reference is updated in
    the secondary databases.  (EG. The plane/ship/land units use a
    secondary database that is indexed by x and y.)

    Second, there is an automatic detection of updated items.  Any time an
    update is made to the database, an entry is filed in a special 'update'
    database.  This is used by the Tk graphics routines to ensure that only
    updated information is redrawn.  Since Tk redraws tend to be very time
    consuming, partial redraws become extremely important.

    Note: Don't manually update the dictionaries with inserts,
    modifications, or deletes.  All changes should be done through the
    updates() method.  (To delete a value, update its value to None.)
    """
    def __getstate__(self):
        """Pickle module handler: determines what will be saved."""
        # Compress dictionary to header and value tuples.
        headers = self.__arrangeHeaders()
        # Preallocate the lists
        revrng = range(len(headers)-1, 0, -1)
        totalList = [None]*len(self.primary)
        i = 0
        for dict in self.primary.values():
            subList = map(dict.get, headers)
            # Eliminate trailing None values.
            for j in revrng:
                if subList[j] is not None:
                    break
            del subList[j+1:]
            totalList[i] = subList
            i = i + 1

        return {'primary_keytype': self.primary_keytype,
                'primary_headers' : headers,
                'primary_values': totalList,
                'timestamp': self.timestamp,
                'secondary_keys': self.secondary.keys()}
    def __setstate__(self, state):
        """Pickle module handler: restore a saved class."""
        pri_keytype = self.primary_keytype = state['primary_keytype']
        self.timestamp = state['timestamp']
        self.unofficial_timestamp = state['timestamp']
        seckeys = state['secondary_keys']

        headers = state['primary_headers']
        valueList = state['primary_values']

        # Convert compressed header/value tuples to a dictionary
        self.primary = primary = {}
        for valTuple in valueList:
            pri_val = {}
            for i in range(len(valTuple)):
                val = valTuple[i]
                if val is not None:
                    pri_val[headers[i]] = val
            pri_key = tuple(map(operator.getitem,
                                (pri_val,)*len(pri_keytype),
                                pri_keytype))
            primary[pri_key] = pri_val

        # rebuild secondary indexes
        self.secondary = secondary = {}
        for sec_type in seckeys:
            secondary[sec_type] = secIndex = {}
            for pri_key, pri_val in primary.items():
                sec_key = tuple(map(pri_val.get, sec_type))
                try: secIndex[sec_key][pri_key] = pri_val
                except KeyError: secIndex[sec_key] = {pri_key: pri_val}

        # List of items that have recently changed
        self.uDB = {}

        # Initialize some handlers
        self.get = primary.get
        self.items = primary.items
        self.values = primary.values
        self.keys = primary.keys
        self.has_key = primary.has_key
    def __init__(self, key, *seckeys):
        # Initialization the class - called at creation time only.
        self.__setstate__({'primary_keytype': key,
                           'primary_headers': [],
                           'primary_values' : [],
                           'timestamp': 0,
                           'secondary_keys': seckeys})
    def __getitem__(self, k):
        return self.primary[k]

    def __arrangeHeaders(self):
        """Return a list of all headers sorted by frequency."""
        headers = {}
        for dict in self.primary.values():
            for j in dict.keys():
                if headers.has_key(j):
                    headers[j] = headers[j] + 1
                else:
                    headers[j] = 1
        lst = map(list, headers.items())
        for i in lst:
            i.reverse()
        lst.sort()
        lst.reverse()
        lst = map(operator.getitem, lst, (1,) * len(lst))
        return lst

    def updates(self, list, returnRemaining=0):
        """Update the database with the items stored in LIST.

        Given a list of dictionary types, extract the primary key from each
        dict, and add the item to the primary, secondary, and update
        databases.
        """
        # Python optimization - copy frequently used variables into
        # local namespace.
        self__primary=self.primary;self__primary_keytype=self.primary_keytype
        self__secondary__items=self.secondary.items();self__uDB=self.uDB
        operator__delitem=operator.delitem;operator__getitem=operator.getitem
        __tuple=tuple;__map=map;__len=len

        if returnRemaining:
            # This flag instructs the routine to return all items in the
            # database that were _not_ updated during this call.
            remainingList = self__primary.copy()
        for dict in list:
            # find the key
            pri_key = __tuple(__map(operator__getitem,
                                    (dict,)*__len(self__primary_keytype),
                                    self__primary_keytype))

            # list all items being deleted
            dict__items = dict.items()
            keys = __map(operator__getitem, dict__items
                         , (0,)*__len(dict__items))
            values = __map(operator__getitem, dict__items
                           , (1,)*__len(dict__items))
            delList = []
            try:
                while 1:
                    pos = values.index(None)
                    delList.append(keys[pos])
                    del keys[:pos+1], values[:pos+1]
            except ValueError:
                pass

            # find dictionary corresponding to key, and place
            # in local variable d
            try:
                d = self__primary[pri_key]
            except KeyError:
                # New key
                d = self__primary[pri_key] = {}
            else:
                # Key already present

                # Remove this item from the returnRemaining list
                if returnRemaining:
                    del remainingList[pri_key]

                # Don't update entries if no changes are made.  Although
                # this may be an expensive operation, the most expensive
                # operations (by far) are screen redraws - any code that
                # reduces redraws will improve performance.
                for key, value in dict__items:
                    try:
                        if d[key] != value:
                            break
                    except KeyError:
                        break
                else:
                    # The 'for loop' completed without an exception,
                    # and without any differences encountered - no
                    # changes present.
                    continue

                # Remove key from the secondary indexes
                for sec_type, sec_db in self__secondary__items:
                    sec_key = __tuple(__map(d.get, sec_type))
                    del sec_db[sec_key][pri_key]
                    if not sec_db[sec_key]:
                        del sec_db[sec_key]

            # Add item to the primary database
            self__primary[pri_key].update(dict)
            # Remove items selected for deletion
            __map(operator__delitem, (self__primary[pri_key],)*__len(delList)
                  , delList)
            # Add item to the updateDB
            self__uDB[pri_key] = d
            # Add key to the secondary indexes
            for sec_type, sec_db in self__secondary__items:
                sec_key = __tuple(__map(d.get, sec_type))
                try: sec_db[sec_key][pri_key] = d
                except KeyError: sec_db[sec_key] = {pri_key:d}
        if returnRemaining:
            return remainingList
    def getSec(self, sec_type):
        """Return the secondary index (a dictionary) for SEC_TYPE."""
        return self.secondary[sec_type]
    def __repr__(self):
        return repr(self.primary)
    def __str__(self):
        return string.join(map(str, self.primary.items()), "\n")

###########################################################################
#############################  Country class  #############################

# Country id for the current player.
CN_OWNED = -1
# Country id for non-owned, and non-deity owned items.
CN_ENEMY = -2
# Country id for non-owned items.
CN_UNOWNED = -3

class Countries:
    """Track empire countries by name or number.

    Note: There will generally be only one instance of this class -
    megaDB['countries'].

    This class is used to solve one basic problem of tracking empire
    countries - sometimes the server returns a country name, other times it
    returns a country number, and other times it will returns both.  To
    solve this, the local databases store owners solely by country number;
    code can call back to this class when the name is desired.  When a
    country is identified by the server solely as a name, this class will
    attempt to resolve it to a number, or if that is not possible it will
    track the name until a number can be resolved for it.
    """
    uDB = {}

    def __getstate__(self):
        return {'unresolved':self.unresolved,
                'nameList':self.nameList,
                'idList': self.idList,
                'player': self.player}
    def __setstate__(self, state):
        self.unresolved = state['unresolved']
        self.nameList = state['nameList']
        self.idList = state['idList']
        self.player = state['player']
    def __init__(self):
        self.__setstate__({'unresolved': {},
                           'nameList': {},
                           'idList': {CN_OWNED:"Owned", CN_ENEMY:"Enemy",
                                      CN_UNOWNED:"Unowned", None:"Unknown",
                                      0:"Deity"},
                           'player': CN_OWNED})

    def getName(self, id):
        """Return a name for a country identified by ID."""
        uid = id
        if id == -1:
            uid = self.player
        try:
            return "(%s) %s" % (uid, self.idList[id])
        except KeyError:
            return "(%s)" % uid

    def getId(self, id):
        """Return an empire Id for the country represented by token ID."""
        if id == CN_OWNED:
            return self.player
        return id

    def getList(self):
        """Return a list of all countries."""
        max = megaDB['version']['maxCountries']
        rng = range(max)
        lst = map(None, rng, map(self.idList.get, rng, [""]*max))
        lst.sort
        return lst

    def resolveName(self, name, dbname, key):
        """Return a token for the country represented by name."""
        try:
            return self.nameList[name]
        except KeyError:
            # A country name with no currently available country Id.
            try: list = self.unresolved[name]
            except KeyError: list = self.unresolved[name] = []
            list.append((dbname, key))
            return name

    def resolveId(self, id):
        """Return a token for the country represented by ID."""
        if id == self.player:
            return CN_OWNED
        return id

    def resolveNameId(self, name, id):
        """Return a token for the country; resolve any outstanding names."""
        if id == self.player:
            self.foundResolotion(name, CN_OWNED)
            return CN_OWNED
        self.foundResolotion(name, id)
        return id

    def resolvePlayer(self, name, id):
        """Note the current player's id and name."""
        self.player = id
        self.foundResolotion(name, CN_OWNED)
        return CN_OWNED

    def foundResolotion(self, name, id):
        """Attempt to resolve a name/id pair."""
        # Check if there are any outstanding names in the database
        # that should be updated with the newly found id.
        if self.unresolved.has_key(name):
            list = self.unresolved[name]
            for dbname, key in list:
                db = megaDB[dbname][key]
                # HACK++
                if db['owner'] == name:
                    db['owner'] = id
            del self.unresolved[name]
        # Update the actual database.
        self.nameList[name] = id
        self.idList[id] = name

###########################################################################
#############################  Time class     #############################
s_time = (r"(?P<day>\S\S\S) (?P<month>\S\S\S) +(?P<date>\d+) (?P<hour>\d+)"
          +r":(?P<minute>\d+):(?P<second>\d+)(?: (?P<year>\d\d\d\d))?")
class EmpTime:
    """Track the empire server time.

    Note: There will generally be only one instance of this class -
    megaDB['time'].

    This code is used to guess at what time it is at the server.  It is
    mainly used to try and approximate when the next update will trigger.
    Times are noted by the various parsers, and sent to this class (via
    megaDB['time']) to note the time.
    """
    Months = {"Jan":1, "Feb":2, "Mar":3, "Apr":4, "May":5, "Jun":6,
              "Jul":7, "Aug":8, "Sep":9, "Oct":10, "Nov":11, "Dec":12}
    Days = {"Mon":0, "Tue":1, "Wed":2, "Thu":3, "Fri":4, "Sat":5, "Sun":6}
    def __getstate__(self):
        return {'nextUpdate': self.nextUpdate}
    def __setstate__(self, state):
        self.nextUpdate = state['nextUpdate']

        self.uDB = {}
        self.observedDrift = None
        self.guessYear = time.localtime(time.time())[0]
    def __init__(self):
        self.__setstate__({'nextUpdate': None})
## 	self.timeDiff = 0.0

    def translateTime(self, match):
        """Convert a regular expression processed time string to local time."""
        year = match.group('year')
        if year is None:
            year = self.guessYear
        else:
            year = self.guessYear = int(year)
        tt = tuple(map(int,
                       match.group('date', 'hour', 'minute', 'second')))
        tt = (year, self.Months[match.group('month')]) + tt + (
            self.Days[match.group('day')], 0, 0)
        tt = time.mktime(tt)
        return tt
    def noteTime(self, match):
        """Note the time from an empire server string."""
## 	tt = self.translateTime(match) + self.timeDiff
        tt = self.translateTime(match)
        ct = time.time()
        drift = ct - tt
        if self.observedDrift is None:
            self.observedDrift = drift
            self.uDB['drift'] = drift
        else:
            variance = self.observedDrift - drift
            if variance < -300.0 or variance > 300.0:
                # Something odd is happenining - reset the drift
                viewer.Error("PTkEI - time oddity..")
                self.observedDrift = drift
                self.uDB['drift'] = drift
            elif self.observedDrift > drift:
                self.observedDrift = drift
                if variance > 0.5:
                    self.uDB['drift'] = drift
## 	    print "local:%s server:%s drift:%s offset:%s" % (
## 		ct, tt, self.observedDrift[0], self.timeDiff)

    def printTime(self, epoch):
        """Print a server time using localtimes."""
        drift = self.observedDrift
        if drift is None:
            drift = 0.0
        return time.ctime(epoch+drift)

##     def noteTimestamp(self, match, ts):
## 	tt = self.translateTime(match)
## 	self.timeDiff = ts-tt
## 	self.noteTime(match)
    def noteNextUpdate(self, match):
        """Make a note of the next update."""
## 	self.nextUpdate = self.translateTime(match) + self.timeDiff
        self.nextUpdate = self.translateTime(match)
    def getCountDown(self):
        """Return a tuple containing the time until the next update."""
        if self.nextUpdate is None:
            # No time received from server yet.
            return (None, None, None)
        drift = self.observedDrift
        if drift is None:
            drift = 0.0
        count = self.nextUpdate - time.time() + drift
        count = divmod(count, (megaDB['version']['ETUSeconds']
                               * megaDB['version']['updateETUs']))[1]
        r, seconds = divmod(count, 60)
        hours, minutes = divmod(r, 60)
        return (int(hours), int(minutes), int(seconds))

###########################################################################
#############################  Useful functions ###########################

#######  Tools for working with sectors.
#######

pathDirections = "ujnbgy"
pathReverseDirections = "bgyujn"
pathOffsets = ((1, -1), (2, 0), (1, 1), (-1, 1), (-2, 0), (-1, -1))

def sectorWrap(coord):
    """Return a unique (x,y) pair from an arbitrary (x,y) pair."""
    maxx, maxy = megaDB['version']['worldsize']
    halfx = maxx/2
    halfy = maxy/2
    return ((coord[0] + halfx)%maxx - halfx,
            (coord[1] + halfy)%maxy - halfy)

def sectorDistance(coordsA, coordsB):
    """Return the absolute distance between two sectors."""
    xa, ya = coordsA
    xb, yb = coordsB
    size_x, size_y = megaDB['version']['worldsize']
    dx = min(abs((xb-xa) % size_x), abs((xa-xb) % size_x))
    dy = min(abs((yb-ya) % size_y), abs((ya-yb) % size_y))
    d = min(dx, dy)
    return d + max((dx - d) / 2, dy - d)

def sectorNeighbors(coord):
    """Return a list of all the sectors surrounding COORD."""
    x, y = coord
    maxx, maxy = megaDB['version']['worldsize']
    halfx = maxx/2
    halfy = maxy/2
    neighbors = []
    for xoff, yoff in pathOffsets:
        neighbors.append(((x + xoff + halfx)%maxx - halfx,
                          (y + yoff + halfy)%maxy - halfy))
    return neighbors

def directionToSector(coord, direc):
    """Return a new sector from a sector and ascii direction."""
    offset = pathOffsets[string.index(pathDirections, direc)]
    maxx, maxy = megaDB['version']['worldsize']
    halfx = maxx/2
    halfy = maxy/2
    return ((coord[0] + offset[0] + halfx)%maxx - halfx,
            (coord[1] + offset[1] + halfy)%maxy - halfy)


#######  Tools for interacting with the database.
#######

def GetPrompt():
    """Return a string with the main prompt."""
    ndb = megaDB['prompt']
    inform, minutes, btus = ndb['inform'], ndb['minutes'], ndb['BTU']
    if inform:
        return "(%s) [%d:%d] Command : " % (inform, minutes, btus)
    return "[%d:%d] Command : " % (minutes, btus)

###########################################################################
#############################  Useful functions ###########################

class DatabaseSaver:
    """Wrapper class for database IO.

    This class is used as a wrapper when reading/writing the database to
    disk.  It isn't used when accessing the database - calls to megaDB hit
    the database directly.  This class is used only for disk IO.

    This class has three public attributes:
        filename - the name of the file that stores the database.
        newDatabase - Boolean flag determines if this is a new database.
        needSave - Boolean flag that determines if the database should be
                saved upon exiting the client.

    The attributes newDatabase and needSave are both set externally from
    this class.  They are reset in the empQueue module when a connection is
    made to an empire server.

    Note: There is generally only one instance of this class - empDb.DBIO.
    """
    dbError = "Error saving/loading the database."
    DBVersion = 32.3

    def reset(self):
        """Reset the main database to an initial state.

        This function should only be used when off-line.

        Note: This should be used with care - it will wipe all known
        information.
        """
        global assist
        global predict
        global megaDB
        megaDB = {
            'DB_Version': self.DBVersion,
            'SECTOR': dictDB(('x', 'y')),
            'SHIPS': dictDB(('id',), ('x', 'y')),
            'PLANES': dictDB(('id',), ('x', 'y')),
            'LAND UNITS': dictDB(('id',), ('x', 'y')),
            'NUKES': dictDB(('x', 'y', 'type'), ('x', 'y')),
            'LOST ITEMS': dictDB(('type', 'id', 'x', 'y')),
            'sectortype': {' ': {}},
            'coordtable' : {},
            'planetype' : {},
            'shiptype' : {},
            'landtype' : {},
            'login': {'host':"localhost", 'port':6665,
                      'coun':"visitor", 'repr':"visitor"},
            'version': {
                'worldsize':(255,255), 'maxCountries':255, 'ETUSeconds':1024,
                'updateETUs':1024, 'minutesOnline':0, 'BTURate':1.0,
                'growRate':1.0, 'harvestRate':1.0, 'birthRate':1.0,
                'UBirthRate':1.0, 'eatRate':1.0, 'BEatRate':1.0,
                'barInterest':1.0, 'civTax':1.0, 'UWTax':1.0, 'milCost':1.0,
                'reserveCost':1.0, 'happyRatio':1, 'educationRatio':1,
                'happyAverage':1, 'educationAverage':1, 'techBoost':1.0,
                'levelDecline':1, 'techLog':1.0, 'techBase':1.0,
                'objectMax':[1,1,1,1], 'objectMob':[1,1,1,1],
                'objectEff':[1,1,1,1], 'fireRange':1.0,
                'enabledOptions':[], 'disabledOptions':[]
                },

            'nation':{'status':"", 'capital':(),
                      'budget':0.0, 'reserves':0, 'education':0.0,
                      'happiness':0.0, 'technology':0.0, 'research':0.0,
                      'techFactor':0.0, 'plagueFactor':0.0,
                      'maxPopulation':9999,
                      'maxCiv':9999, 'maxUW':9999, 'happyNeeded':0.0},
            'realm': {},
            'announcements': {'last':(), 'list':[]},
            'telegrams': {'last':(), 'list':[]},
            'countries': Countries(),
            'prompt': {'minutes':0, 'BTU':0, 'inform':""},
            'time': EmpTime(),
            }
        self.resetUpdate()
        self.newDatabase = 1
        self.needSave = 0

    def resetUpdate(self):
        """Reset the update database."""
        global updateDB
        updateDB = {
            'SECTOR': megaDB['SECTOR'].uDB,
            'SHIPS': megaDB['SHIPS'].uDB,
            'PLANES': megaDB['PLANES'].uDB,
            'LAND UNITS': megaDB['LAND UNITS'].uDB,
            'NUKES': megaDB['NUKES'].uDB,
            'LOST ITEMS': megaDB['LOST ITEMS'].uDB,
            'sectortype': {' ': {}},
            'coordtable' : {},
            'planetype' : {},
            'shiptype' : {},
            'landtype' : {},
            'version': {},
            'nation': {},
            'realm': {},
            'announcements': {},
            'telegrams': {},
            'countries': megaDB['countries'].uDB,
            'prompt': {},
            'time': megaDB['time'].uDB
            }

    def load(self, filename):
        """Load database from FILE.

        If the file doesn't exist, create a default database.

        This function should only be used when off-line.
        """
        self.filename = filename
        global megaDB
        try:
            fl = open(filename, "rb")
        except IOError:
            self.reset()
        else:
            megaDB = cPickle.load(fl)
            if megaDB['DB_Version'] != self.DBVersion:
                raise self.dbError, (
                    "PTkEI: Database has an incorrect version number.")
            fl.close()
            self.newDatabase = 0
            self.needSave = 0
            self.resetUpdate()
        if not megaDB.has_key('planetype'):
            megaDB['planetype'] = {}
            megaDB['shiptype'] = {}
            megaDB['landtype'] = {}

    def save(self):
        """Write the database back to disk."""
        if not self.needSave:
            # No need to save anything
            return
        print "PTkEI: Saving DB to '%s'.." % self.filename
        fl = open(self.filename, 'wb')
        cPickle.dump(megaDB, fl, 1)
        fl.close()

DBIO = DatabaseSaver()
