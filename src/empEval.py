"""Allows embedded python expressions to reference the internal database."""

#    Copyright (C) 1998-1999 Kevin O'Connor
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

import string
import re
import operator
import sys

import empDb
import empParse


# Key Ideas:

# What is contained within this file:

# This file supports execution of arbitrary python expression that are
# embedded in strings.  Basically, this means queries like "foreach *
# ?civ=9 move c [sect] [civ/2] [dist]" can be made.  There are two main
# parts to the processing of python expressions.  The first is the
# conversion of empire selectors into python expressions.  The string "*
# ?civ=9" can be converted to a valid python expression by selectToExpr().
# The string "move c [sect] [civ/2] [dist]" is converted in the function
# estrToExpr().  The second major part is the application of these
# expressions to the database.  The function getSectors() takes a valid
# python expression, tests every sector in a given database, and then
# returns a list of all sectors that tested true for that expression.  The
# function evalString takes an embedded python expression and returns a
# string result.  The function foreach() is a combination of getSectors()
# and evalString() - given an arbitrary python test-expression and an
# arbitrary python string-expression, for every element in a database that
# tests true it returns an evaluation of the string.


# How the evaluation occurs:

# For performance reasons, the method used to achieve these evaluations is
# rather cumbersome.  For each database that can be queried, an instance of
# the class delayedBinding is created.  The delayedBinding class basically
# defines all the operator-overloading methods supported by python
# (__add__, __mul__, etc.).  When one of these class methods is invoked,
# the actual variable reference is extracted from a class variable
# (delayedValue).  (The variable delayedValue is essentially a global
# variable - this class is not multi-threaded safe.)  The instance then
# simulates the requested operation with this extracted variable. By
# delaying the binding of delayedValue until the actual time of the desired
# operation, the class can get away with delaying or avoiding the cost of
# an entire database conversion.  This leads to a significant improvement
# in performance; however, the methods used are questionable at best - it
# may be replaced sometime in the future.

###########################################################################
#############################  Evaluate Class   ###########################

class delayedBinding:
    """Delays a binding of a variable until runtime.

    This is a total hack!
    """
    delayedValue = None
    operator = operator
    for i, j in [
        ('__add__', 'self.operator.add'), ('__sub__', 'self.operator.sub'),
        ('__mul__', 'self.operator.mul'), ('__div__', 'self.operator.div'),
        ('__mod__', 'self.operator.mod'),
        ('__lshift__', 'self.operator.lshift'),
        ('__rshift__', 'self.operator.__rshift__'),
        ('__and__', 'self.operator.__and__'),
        ('__or__', 'self.operator.__or__'), ('__xor__', 'self.operator.xor'),
        ('__concat__', 'self.operator.concat'),
        ('__repeat__', 'self.operator.repeat'),
        ('__cmp__', 'cmp'), #('__coerce__', 'coerce'),
        ]:
        exec ("def "+i+"(self, other):\n"
              +" return "+j+"(self.convertField(), other)\n")
    for i, j in [
        ('__radd__', 'self.operator.add'), ('__rsub__', 'self.operator.sub'),
        ('__rmul__', 'self.operator.mul'), ('__rdiv__', 'self.operator.div'),
        ('__rmod__', 'self.operator.mod'),
        ('__rlshift__', 'self.operator.lshift'),
        ('__rrshift__', 'self.operator.__rshift__'),
        ('__rand__', 'self.operator.__and__'),
        ('__ror__', 'self.operator.__or__'), ('__rxor__', 'self.operator.xor'),
        ]:
        exec ("def "+i+"(self, other):\n"
              +" return "+j+"(other, self.convertField())\n")
    for i, j in [
        ('__neg__', 'self.operator.neg'), ('__pos__', 'self.operator.pos'),
        ('__abs__', 'self.operator.abs'), ('__invert__', 'self.operator.inv'),
        ('__not__', 'self.operator.__not__'),
        ('__int__', 'int'), ('__long__', 'long'), ('__float__', 'float'),
        ('__oct__', 'oct'), ('__hex__', 'hex'),
        ('__nonzero__', 'self.operator.truth'),
        ('__hash__', 'hash'), ('__str__', 'str'), ('__repr__', 'repr')
        ]:
        exec ("def "+i+"(self):\n"
              +" return "+j+"(self.convertField())\n")
    def __init__(self, name):
        self.name = name
    def __call__(self, *args, **kw):
        return apply(self.convertField(), args, kw)
    def convertField(self):
        try:
            if callable(self.name):
                val = self.name(self.delayedValue)
            else:
                val = self.delayedValue[self.name]
        except KeyError, e:
            raise NameError, e
##  	try:
##  	    val = empDb.fixedAtoI(val)
##  	except ValueError:
##  	    try:
##  		val = float(val)
##  	    except ValueError:
##  		pass
##  	except TypeError:
##  	    pass
        return val

###########################################################################
#############################  Empire Selectors ###########################

# Conversion of empire selectors to local database format.
# Note: This was taken from the html info pages.
def initializeSelectors():
    baseConversion = [
        ('xloc', 2, 'x'), ('yloc', 2, 'y'), ('owner', 2),
        ##	('timestamp',),

        # Added identifier:
        ('sect', 3, (lambda ldb:
                     ("%s,%s" % (ldb['x'], ldb['y'])))),
        # Function that reports sector distance -- distance(x,y)
        ('distance', 8, (lambda ldb:
                         (lambda x, y, __fromx=ldb['x'], __fromy=ldb['y']:
                          (empDb.sectorDistance((__fromx, __fromy), (x, y))))))
        ]

    commodityConversion = [
        ('civil', 2, 'civ'), ('milit', 3, 'mil'), ('shell', 2), ('gun', 2),
        # Yuck, sometimes this is 'pet', othertimes 'petrol'
        ##	('petrol',),
        ('iron', 2), ('dust', 2), ('bar', 2), ('food', 2), ('oil', 2),
        ('lcm', 2), ('hcm', 2), ('uw', 2), ('rad', 3),
        ]

    sectorConversion = baseConversion + commodityConversion + [
        ('des', 2),
        ('effic', 2, 'eff'), ('mobil', 2, 'mob'),
        ('terr', 2), ('terr1', 5), ('terr2', 5), ('terr3', 5),
        ('road', 2), ('rail', 2), ('dfense', 2, 'defense'),
        ('work', 2), ('coastal', 2, 'coast'),
        ('newdes', 2, (lambda ldb:
                       (ldb['sdes'] == '_' and ldb['des'] or ldb['sdes']))),
    ##     ('newdes', 2, "(sdes != '_' and sdes or des)"),
        ('min', 2), ('gold', 2),
        ('fert', 2), ('ocontent', 2), ('uran', 2),
        ('oldown', 2),
        ('off', 2), ('xdist', 2, 'dist_x'), ('ydist', 2, 'dist_y'),
        ('avail', 2),

        ('petrol', 2, 'pet'),

        ('c_dist', 4), ('m_dist', 4), ('u_dist', 4), ('s_dist', 4),
        ('g_dist', 4), ('p_dist', 4), ('i_dist', 4), ('d_dist', 4),
        ('b_dist', 4), ('f_dist', 4), ('o_dist', 4), ('l_dist', 4),
        ('h_dist', 4), ('r_dist', 4),
        ('c_del', 4, 'c_cut'), ('m_del', 4, 'm_cut'), ('u_del', 4, 'u_cut'),
        ('s_del', 4, 's_cut'), ('g_del', 4, 'g_cut'),
        ('p_del', 4, 'p_cut'), ('i_del', 4, 'i_cut'), ('d_del', 4, 'd_cut'),
        ('b_del', 4, 'b_cut'), ('f_del', 4, 'f_cut'),
        ('o_del', 4, 'o_cut'), ('l_del', 4, 'l_cut'), ('h_del', 4, 'h_cut'),
        ('r_del', 4, 'r_cut'),

        # Added identifier:
        ('dist', 2, (lambda ldb:
                     ("%s,%s" % (ldb['dist_x'], ldb['dist_y']))))
        ]

    unitsConversion = baseConversion + [
        ('type', 2),
        ('effic', 2, 'eff'), ('mobil', 2, 'mob'),
        ##  ('sell',),
        ('tech', 2), ('uid', 2, 'id'),

        ##	('group',) # Hrmm. this really should be in each subgroup

        ##	('opx',), ('opy',), ('mission'),
        ]

    shipConversion = commodityConversion + unitsConversion + [
        ('fleet', 2, 'flt'), ('nplane', 2, 'pln'), ('fuel', 2),
        ('nxlight', 2,'xl'), ('nchoppers', 3, 'he'),
        ##	('autonav'),

        ('group', 2, 'flt'),
        ('petrol', 2),
        ]

    planeConversion = unitsConversion + [
        ('wing', 2), ('range', 2), ('ship', 2), ('att', 2),
        ('def', 2), ('harden', 2, 'hard'), ('nuketype', 2, 'nuke'),
        ##	('flags',),
        ('land', 2),

        ('group', 2, 'wing'),
        ]

    landConversion = commodityConversion + unitsConversion + [
        ('att', 2), ('def', 2), ('army', 4), ('ship', 2),
        ('harden', 2, 'fort'), ('retreat', 2, 'retr'), ('fuel', 2),
        ('land', 2), ('nxlight', 2, 'xl'),

        ('group', 2, 'army'),
        ('petrol', 2),
        ]

    nukeConversion = baseConversion + [
        ('number', 2, 'num'),
        ##	('ship',), ('trade',), ('timestamp'),
        ]

    versionDB = [
        ('xmax', 2, (lambda ldb: ldb['worldsize'][0])),
        ('ymax', 2, (lambda ldb: ldb['worldsize'][1])),
        ]

    nationDB = [
        ('cmax', 2, 'maxCiv'),
        ('umax', 2, 'maxUW'),
        ]

    def createConversionDB(list):
        dict = {}
        for i in list:
            if len(i) < 3:
                val = i[0]
            else:
                val = i[2]
            delayedVar = delayedBinding(val)
            for j in range(i[1], len(i[0])+1):
                dict[i[0][:j]] = delayedVar
        return dict

    # Initialize the execution eviornments for database evaluations.
    global selectors
    selectors = {
        'SECTOR': createConversionDB(sectorConversion),
        'SHIPS': createConversionDB(shipConversion),
        'PLANES': createConversionDB(planeConversion),
        'LAND UNITS': createConversionDB(landConversion),
        'NUKES': createConversionDB(nukeConversion),
        'nation': createConversionDB(nationDB),
        'version': createConversionDB(versionDB),
        }

    # Initialize a commodity transformation dictionary:
    global commodityTransform
    commodityTransform = {}
    for i in (
        ('civil', 'civ'), ('milit', 'mil'), ('shell', 'shell'),
        ('gun', 'gun'), ('petrol', 'pet'), ('iron', 'iron'),
        ('dust', 'dust'), ('bar', 'bar'), ('food', 'food'),
        ('oil', 'oil'), ('lcm', 'lcm'), ('hcm', 'hcm'), ('uw', 'uw'),
        ('rad', 'rad')):
        for j in range(len(i[0])):
            commodityTransform[i[0][:j+1]] = i[1]

initializeSelectors()


error = "empEval error"


###########################################################################
############################# Convert functions ###########################

s_realm = r"#(?P<realm>\d*)"
s_sectors = (r"(?P<minX>"+empParse.ss_sect+")(?::(?P<maxX>"
             +empParse.ss_sect+"))?,(?P<minY>"+empParse.ss_sect
             +")(?::(?P<maxY>"+empParse.ss_sect+"))?")
s_circular = (r"@(?P<cirX>"+empParse.ss_sect+"),(?P<cirY>"+empParse.ss_sect
              +"):(?P<cirD>\d+)")
sectorsFormat = re.compile("^\*$|^"+s_realm+"$|^"+s_sectors
                           +"$|^"+s_circular+"$")
conditionsFormat = re.compile(
    r"^(?P<var>\S+?)(?P<opr>[=<>#])(?P<val>\S+?)(?:&(?P<next>\S+))?$")
def selectToExpr(dbname, range, cond):
    """Convert a standard empire range/selectors to a python expression.

    This takes a range of the form 'x1:x2,y1:y2', 'x,y', '#?', or '*' (all
    the possible empire ranges) and a cond of the form 'var[#=<>]var&...',
    and converts it to a valid python expression.  (IE. 'xl>=x1 and xl<=x2
    and yl>=y1 and yl<=y2 and var==var and ...').  The result of this can
    then be passed to getSectors or foreach to return a list of db items
    that apply.

    Note: This function does not check for ownership.  Frequently, the
    string 'owner==-1 and ' is preprended to the output of this function to
    force it to only apply to owned objects.
    """
    mc = sectorsFormat.match(range)
    if not mc:
        raise error, "Coordinate regexp failure."

    if mc.group('realm') is not None:
        # Realm
        if mc.group('realm') == "":
            rm = 0
        else:
            rm = int(mc.group('realm'))
        try: val = empDb.megaDB['realm'][rm]
        except KeyError:
            raise error, "Realm not in database."
        minX, maxX, minY, maxY = val
        if minX < maxX: 
            conditions = map(operator.add, ("xl>=", "xl<="),
                             map(str, (minX, maxX)))
        elif minX > maxX:
            conditions = ["(xl >= %d or xl <= %d)" % (minX, maxX)]
        else:
            conditions = ["xl==%d" % (minX)]
        if minY < maxY: 
            conditions = conditions + map(operator.add, ("yl>=", "yl<="),
                                          map(str, (minY, maxY)))
        elif minY > maxY:
            conditions.append("(yl >= %d or yl <= %d)" % (minY, maxY))
        else:
            conditions.append("yl==%d" % (minY))
    elif mc.group('minX'):
        # Range
        if mc.group('maxX'):
            minX, maxX = map(int, mc.group('minX', 'maxX'))
            if minX < maxX: 
                conditions = map(operator.add, ("xl>=", "xl<="),
                                 mc.group('minX', 'maxX'))
            elif minX > maxX:
                conditions = ["(xl >= %s or xl <= %s)" % mc.group('minX', 'maxX')]
        else:
            conditions = ["xl==" + mc.group('minX')]
        if mc.group('maxY'):
            minY, maxY = map(int, mc.group('minY', 'maxY'))
            if minY < maxY: 
                conditions = conditions + map(operator.add, ("yl>=", "yl<="),
                                 mc.group('minY', 'maxY'))
            elif minY > maxY:
                conditions.append("(yl >= %s or yl <= %s)" % mc.group('minY', 'maxY'))
        else:
            conditions.append("yl==" + mc.group('minY'))
    elif mc.group('cirX'):
        # Circular area
        conditions = ["distance(%s,%s)<=%s" % mc.group('cirX', 'cirY', 'cirD')]
    else:
        # All ('*') selection
        conditions = []

    # Convert selectors into an eval string
    while cond:
        mc = conditionsFormat.match(cond)
        if not mc:
            raise error, "Condition regexp failure."
        # Convert the two variables
        vars = []
        for i in mc.group('var', 'val'):
            if len(i) == 1 and not i in string.digits:
                vars.append(repr(i))
            elif re.compile("^[a-z][a-z0-9_]+$").match(i) and not selectors[dbname].has_key(i):
                vars.append(repr(i))
            else:
                vars.append(i)
        conditions.append("%s%s%s" % (
            vars[0],
            {'=':'==', '#':'!=', '<':'<', '>':'>'}[mc.group('opr')],
            vars[1]))
        cond = mc.group('next')

    if not conditions:
        return "1"
    return string.join(conditions, " and ")

ss_normal = "[^\]\"']"
ss_quoted1 = "'.*?'"
ss_quoted2 = '".*?"'
s_pre = r"(?P<pre>.*?)"
s_eval = r"(?P<eval>(?:"+ss_normal+"|"+ss_quoted1+"|"+ss_quoted2+")*)"
s_post = r"(?P<post>.*)"
exprFormat = re.compile("^"+s_pre+"\["+s_eval+"\]"+s_post+"$")
def estrToExpr(txt):
    """Convert a string with embedded python expressions to an expression.

    This takes a string of the form 'text_1 [expr1] text_2 [expr2] ...' and
    converts it to ('text_1 '+str(expr1)+' text_2 '+str(expr2)+' ...').
    """
    cmd = ""
    while txt:
        mc = exprFormat.match(txt)
        if not mc:
            cmd = cmd + "+"+`txt`
            break
        cmd = cmd + "+"+`mc.group('pre')`
        e = mc.group('eval')
        txt = mc.group('post')
        cmd = cmd + "+str(("+e+"))"
    return cmd[1:]

###########################################################################
#############################  Eval functions   ###########################

def evalString(expr, dbname, db):
    """Evaluate an expression and return the result."""
    envio = selectors[dbname]
    delayedBinding.delayedValue = db
    try:
        return eval(expr, envio)
    except:
        raise error, (
            'Evaluate error!\n"%s" raised %s with detail:\n"%s".'
            % ((expr,)+tuple(sys.exc_info()[:2])))

def execCodeblock(dbname, execStr):
    """Execute a string for every item in a database.

    This is an internal function that is called by several functions below.
    This is really just useful for code consolidation.  The execStr
    parameter is very specific to the code block found within this
    function.
    """
    # Find every sector that applies
    envio = selectors[dbname]
    exec("def __func(__db, __class):\n"
         +" __list = []\n"
         +" __db = __db.items()\n"
         +" __db.sort()\n"
         +" for __db in __db:\n"
         +"  __class.delayedValue = __db[1]\n"
         +"  try:\n"
         +execStr
         +"  except NameError, e:\n"
         +"   pass\n"
         +" return __list\n", envio)
    f = envio['__func']
    del envio['__func']
    return f(empDb.megaDB[dbname], delayedBinding)

def getSectors(expr, dbname):
    """Given a python expression, return all db keys that apply.

    This functions takes a valid python expression (expr), evaluates it for
    every item in empDb.megaDB[dbname] and then returns a list of all the
    keys that tested true.
    """
    try:
        return execCodeblock(
            dbname,
            "   if ("+expr+"): __list.append(__db[0])\n")
    except:
        raise error, (
            'GetSectors error in "%s"!\nException %s with detail:\n"%s".'
            % ((expr,) + tuple(sys.exc_info()[:2])))

def getSectorDBs(expr, dbname):
    """Given a python expression, return a database with all that apply.

    This functions takes a valid python expression (expr), evaluates it for
    every item in empDb.megaDB[dbname] and then returns a database containg
    all the sector key/value pairs that tested true for the expression.
    """
    try:
        list = execCodeblock(
            dbname,
            "   if (%s): __list.append(__db)\n" % expr)
    except:
        raise error, (
            'GetSectorDBs error in "%s"!\nException %s with detail:\n"%s".'
            % ((expr,) + tuple(sys.exc_info()[:2])))
    dict = {}
    map(apply, [operator.setitem]*len(list),
        map(operator.add, ((dict,),)*len(list), list))
    return dict

##  def getMMoveInfo(commodity, sourceSelect, sourceLevel, sourceMob,
##  		 destSelect, destLevel, move_to, move_from, move_weight):
##      """Specialized data retriever for the mmove class."""
##      try:
##  	slist = execCodeblock(
##  	    'SECTOR',
##  	    "   if ("+sourceSelect+"): "
##  	    +"__list.append(((xloc+0, yloc+0), __db[1], int("
##  	    +commodity+"-("+sourceLevel+")), int(mob-("+sourceMob+"))))\n")
##  	dlist = execCodeblock(
##  	    'SECTOR',
##  	    "   if ("+destSelect+"): "
##  	    +"__list.append(((xloc+0, yloc+0), __db[1], int("
##  	    +destLevel+"-("+commodity+"))))\n")
##      except:
##  	raise error, (
##  	    'GetMMoveInfo error\nException %s with detail:\n"%s".'
##  	    % tuple(sys.exc_info()[:2]))
##      ddict = {}
##      for coord, db, amount in dlist:
##  	if amount > 0 and move_to(db, commodity):
##  	    ddict[coord] = amount
##      sdict = {}
##      for coord, db, amount, mobility in slist:
##  	if (amount > 0 and mobility > 0
##  	    and not ddict.has_key(coord)
##  	    and move_from(db, commodity)):
##  	    sdict[coord] = (amount, mobility,
##  			    move_weight(db, commodity))
##      return (sdict, ddict)

def foreach(cond_expr, txt_expr, dbname):
    """Combination of getSectors and evalString."""
    try:
        return execCodeblock(
            dbname,
            "   if ("+cond_expr+"): __list.append(("+txt_expr+"))\n")
    except:
        raise error, (
            'Foreach error in "%s"/"%s"!\nException %s with detail:\n"%s".'
            % ((cond_expr, txt_expr) + tuple(sys.exc_info()[:2])))
