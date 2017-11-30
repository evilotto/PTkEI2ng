"""Routines for empire sector units."""

# version 1.0.1
#    Copyright (C) 1998 Ulf Larsson
#    Copyright (C) 2013 William Fittge

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
import math

import empDb
import empParse

## to be used for sectors you can't move into
infinite_mob_cost = 99999.9

def to_coord( sect ) :
    """ create Coords type from sector """
    return ( sect[ 'x' ] ,
             sect[ 'y' ] )


def mob_cost( sect ) :
    """ mobility cost to move into a sector """
    min_mob_cost = 0.001
    result = 2.0 * infinite_mob_cost
    d = sect.get( 'des' )
    if is_land( d ) and d != 's' and d != '\\' :
        eff = value( sect, 'eff'  )
        des_mob = type_mcost( d, eff )
        road = value( sect, 'road' )
        result = des_mob - (des_mob * 0.009 * road)
    if result < min_mob_cost :
        result = min_mob_cost
    return result

def type_mcost( des, eff ) :
    """ sector type mobility cost """
    mcost = empDb.megaDB['sectortype'][des.lower()]['mcost']
    zmcost = empDb.megaDB['sectortype'][des.lower()]['zmcost']
    result = zmcost + ((mcost - zmcost) * eff / 100.0)
    return result

def is_land( des ) :
    """ is this a land sector """
    return des and des != ' ' and des != '.' and des != 'x' and des != 'X'

def is_sea( des) :
    """ is this a water sector """
    return des and ( des == '.' or des == 'x' or des == 'X' )

def is_oldowned( sect ) :
    """ are we  oldowner of this sector """
    return sect.get( 'oldown' ) == empDb.CN_OWNED

def is_movable_into( sect, commodity ) :
    """ is it possible to move commodity into sect  """
    return commodity != 'civ' or is_oldowned( sect )

def is_movable_from( sect, commodity ) :
    """ is it possible to move commodity from sect  """
    result = 0
    if is_oldowned( sect ) or commodity == 'mil' :
        result = 1
    else :
        mil = value( sect, 'mil' )
        civ = value( sect, 'civ' )
        result = mil * 10 >= civ
    return result

def is_explorable_into( sect ) :

    des   = sect.get( 'des' )
    owner = sect.get( 'owner' )
    mil   = sect.get( 'mil' )
    civ   = sect.get( 'civ' )

    if ( des is not None ):
        return ( is_land( des ) and des != '\\' and des != 's'
                 and ( ( civ  == 0 and mil == 0 )
                       or ( ( owner == 0 or not owner )
                            and (des == '-' or des == '=' or des == '^' or des == '@') ) ) )

def value( sect, what ) :
    """ atoi that returns 0 on null string """
    return sect.get(what, 0)


def commodity_weight( commodity ) :
    """ weight for different kinds of commodities"""
    result = 1.0
    if commodity == 'bar' :
        result = 50.0
    elif commodity == 'gun' :
        result = 10.0
    elif commodity == 'rad' :
        result = 8.0
    elif commodity == 'dust' :
        result = 5.0
    elif commodity == 'uw' :
        result = 2.0
    return result

def packing_bonus( sect, commodity ) :
    """ packing bonus when moving commodity"""
    result = 1.0
    eff = value( sect, 'eff' )
    des = sect.get( 'des' )
    if des and eff >= 60 :
        if commodity == 'civ' :
            pack = 'pack_civ'
        elif commodity == 'mil' :
            pack = 'pack_mil'
        elif commodity == 'bar' :
            pack = 'pack_bar'
        elif commodity == 'uw' :
            pack = 'pack_uw'
        else :
            pack = 'pack_other'
        result = empDb.megaDB['sectortype'][des][pack]
    return result

def move_weight( sect, commodity ) :
    """ mobility cost multiplier for moving gods out of sector """
    return commodity_weight( commodity ) / packing_bonus( sect,
                                                          commodity )

def new_designation( sect ) :
    new_des = sect.get( 'sdes' )
    if not new_des or new_des == ' ' or new_des == '_' :
        new_des = sect.get( 'des' )
    return new_des

def max_pop( sect ) :
    """Computes the maximum population of a sector.  This function is
    a translation of function 'max_pop' in the 4.2.10 server
    (emp4/src/lib/common/res_pop.c)."""

    des = sect.get( 'des' )

    if not is_land(des) or des == '?':
        return 0
    
    res = empDb.megaDB['nation']['research']
    maxpop = 999
    
    if 'RES_POP' in empDb.megaDB['version']['enabledOptions']:
        maxpop = int((((50.0+4.0*res)/(200.0+3.0*res))*600.0) + 400)
        if maxpop > 999:
            maxpop = 999
            
    if 'BIG_CITY' in empDb.megaDB['version']['enabledOptions']:
        if des == 'c':
            eff = sect.get('eff')
            if eff is None:
                eff = 0
            maxpop = int(maxpop * ((9 * eff) / 100 + 1))

    if des == '^':
        maxpop = maxpop / 10
    elif des == '~':
        maxpop = maxpop / 20
    return maxpop


def food_needed_for_breed( sect ) :
    """ food needed for maximum growth """
    result = 0
    if 'NOFOOD' not in empDb.megaDB['version']['enabledOptions']:
        etu        = version_value( 'UpdateTime' )
        eat_rate   = version_value( 'eat_rate' )
        baby_eat   = version_value( 'baby_eat' )
        uw_brate   = version_value( 'uw_brate' )
        o_brate    = version_value( 'o_brate' )

        food_eaten = eat_rate * etu * (value(sect, 'civ') + value(sect, 'uw')
                                       + value(sect, 'mil'))
        civ_babies = civ_new(sect) - value(sect, 'civ')
        uw_babies = uw_new(sect) - value(sect, 'uw')
        babies_food = (civ_babies + uw_babies) * baby_eat
        result = -math.floor(-(food_eaten + babies_food)) + 1
    return result


##
## All functions below assume that there is enough with food.
##

def civ_new( sect ) :
    """ number of civilians after the update """
    etu        = version_value( 'UpdateTime' )
    o_brate    = version_value( 'o_brate' )
    result = math.floor( ( o_brate * etu + 1.0 ) * value( sect, 'civ' ) )

    if result > max_pop( sect ) :
        result = max_pop( sect )

    return result


def uw_new( sect ) :
    """ number of unemployed workers after the update """
    etu        = version_value( 'UpdateTime' )
    uw_brate   = version_value( 'uw_brate' )

    result = math.floor( ( uw_brate * etu + 1.0 ) * value( sect, 'uw' ) )

    if result > max_pop( sect ) :
        result = max_pop( sect )

    return result


def civ_work( sect ) :
    """ work done by civs during the update """
    etu        = version_value( 'UpdateTime' )
    return  ( etu / 100.0 * civ_new( sect )
              * value( sect, 'work' ) / 100.0 )



def uw_work( sect ) :
    """ work done by uw during the update """
    etu        = version_value( 'UpdateTime' )
    return  etu / 100.0 * uw_new( sect )


def mil_work( sect ) :
    """ work done by mil during the update """
    etu        = version_value( 'UpdateTime' )
    return  etu / 100.0 * value( sect, 'mil' ) * 2.0 / 5.0


def work_force( sect ) :
    """ total amount of available work during the update """
    return civ_work( sect ) + uw_work( sect ) + mil_work( sect )


def eff_new( sect ) :
    """ efficiency of the sector after next update """

    ##             ** BUG **
    ##  This code is wrong since some sector types
    ##  needs hcm and/or lcm to increase effeciency
    ##

    work = work_force( sect )
    eff, work, des = eff_work_new( sect, work )
    return eff, des



def eff_work_new( sect, work ) :
    """ new efficiency and remaining available work of 'work' and new
    type of the sector """ 
    eff = value( sect, 'eff' )
    work = int(work)
    bwork = work / 2
    new_des = new_designation( sect )
    type = sect.get('des')
    
    if new_des != sect.get( 'des' ) :
        twork = (eff + 3) / 4
        if twork > bwork:
            twork = bwork

        work = work - twork
        bwork = bwork - twork
        eff = eff - twork * 4
        if eff <= 0:
            type = new_des
            eff = 0

    twork = 100 - eff
    if twork > bwork:
        twork = bwork

    if sect.get('owner') == empDb.CN_OWNED:
        secttype = empDb.megaDB['sectortype'][new_des]
        if secttype.has_key('lcm_eff') and secttype['lcm_eff'] > 0:
            lcms = sect.get('lcm')
            if lcms is None:
                lcms = 0
            lcms = lcms / secttype['lcm_eff']
            if twork > lcms:
                twork = lcms
        if secttype.has_key('hcm_eff') and secttype['hcm_eff'] > 0:
            hcms = sect.get('hcm')
            if hcms is None:
                hcms = 0
            hcms = hcms / secttype['hcm_eff']
            if twork > hcms:
                twork = hcms
            
    work = work - twork
    eff = eff + twork
    
    return ( eff , work, type )



def work_needed_for_eff( sect, new_eff ) :
    """ work needed to increase efficiency to new_eff """
    old_eff = value( sect, 'eff' )
    if new_designation( sect ) != sect.get( 'des' ) :
        old_eff = - ( old_eff + 3 ) / 4

    return new_eff - old_eff





def civ_needed_for_eff( sect, new_eff ) :
    """ civ needed to increase efficiency to new_eff

    returns zero or a negative value if there is enough
    mil and uw to increase efficincy to new_eff without
    any civ """

    etu        = version_value( 'UpdateTime' )
    o_brate    = version_value( 'o_brate' )

    civ_work_needed = ( 2.0 * work_needed_for_eff( sect, new_eff )
                        - uw_work( sect ) - mil_work( sect ) )

    civ_work_fact = (1.0 + etu * o_brate ) * etu / 100.0

##      return math.floor( civ_work_needed  / civ_work_fact + 1.0 )
    return -math.floor( - civ_work_needed  / civ_work_fact )



def uw_needed_for_eff( sect, new_eff ) :
    """ uw needed to increase efficiency to new_eff

    returns zero or a negative value if there is enough
    civ and mil to increase efficincy to new_eff without
    any uws """

    etu        = version_value( 'UpdateTime' )
    uw_brate   = version_value( 'uw_brate' )

    uw_work_needed = ( 2.0 * work_needed_for_eff( sect, new_eff )
                       - civ_work( sect ) - mil_work( sect ) )

    uw_work_fact = ( 1.0 + etu * uw_brate ) * etu / 100.0

##      return math.floor( uw_work_needed  / uw_work_fact + 1.0 )
    return -math.floor( - uw_work_needed  / uw_work_fact )


def mil_needed_for_eff( sect, new_eff ) :
    """ mil needed to increase efficiency to new_eff

    returns zero or a negative value if there is enough
    civ and uw to increase efficincy to new_eff without
    any mil """

    etu         = version_value( 'UpdateTime' )

    mil_work_needed = ( 2.0 * work_needed_for_eff( sect, new_eff )
                        - civ_work( sect ) - uw_work( sect ) )
    mil_work_fact = ( 2.0 / 5.0 ) * etu / 100.0

##      return math.floor( mil_work_needed  / mil_work_fact + 1.0 )
    return -math.floor( - mil_work_needed  / mil_work_fact )





def work_needed_for_prod( sect ) :
    """ work needed to produce as much as possible """
    prod_work = 0.0
    des = new_designation( sect )

    if des == 'm' :
        mine_cont = value( sect, 'min' );
        if mine_cont > 0.0 :
            prod_work = ( 999.0 * 100.0 ) / mine_cont

    ## work needed to deplete all resources
    ## ** BUG ** isn't correct with GO_RENEW option
    elif des == 'g':
        if value( sect, 'gold' ) > 0.0 :
            prod_work = 500.0

    elif des == 'u':
        if value( sect, 'uran' ) > 0.0 :
            prod_work = 500.0

    elif des == 'o':
        if value( sect,  'ocontent' ) > 0.0 :
            prod_work = 1000.0

    elif des == 'j':
        prod_work = value( sect, 'iron' )
        if prod_work > 999.0 :
            prod_work = 999.0

    elif des == 'k':
        prod_work = value( sect, 'iron' )
        if prod_work > 2.0*999.0 :
            prod_work = 2.0 * 999.0;

    elif des == '%':
        tech = nation_value( 'tech' )
        if tech > 20.0 :
            prod_work = value( sect, 'oil' );
            if prod_work * 10.0 > 999.0 :
                prod_work = 999.0 / 10.0;

    elif des == 'b':
        prod_work = value( sect, 'dust' )
        if prod_work > 5.0 * 999.0  :
            prod_work = 5.0 * 999.0;

    elif des == 'l' or des == 'p':
        prod_work = value( sect, 'lcm' );
        if prod_work > 999.0 :
            prod_work = 999.0;

    elif des == 'i':
        tech = nation_value( 'tech' )
        if tech > 20.0 :
            hcm_max = value( sect, 'hcm' )
            if 2.0 * hcm_max > value ( sect, 'lcm' ) :
                hcm_max = value( sect, 'lcm' ) / 2.0
            if hcm_max > 999.0 :
                hcm_max = 999.0
            prod_work = 3.0 * hcm_max

    elif des == 'd':
        tech = nation_value( 'tech' )
        if tech > 20.0 :
            oil_max = value( sect, 'oil' )
            if  5.0 * oil_max > value( sect, 'lcm' )  :
                oil_max = value( sect, 'lcm' ) / 5.0

            if 10.0 * oil_max > value( sect, 'hcm' ) :
                oil_max = value( sect, 'hcm' ) / 10.0
            if oil_max > 999.0 :
                oil_max = 999.0
            prod_work = ( 1.0 + 5.0 + 10.0 ) * oil_max;

    elif des == 't' or des == 'r':
        edu = nation_value( 'edu' )
        dust_max = 0.0
        if edu > 5.0 :
            dust_max = value( sect, 'dust' )
            if 5.0 * dust_max > value( sect, 'oil' ) :
                dust_max = value( sect, 'oil' ) / 5.0
            if 10.0 * dust_max > value( sect, 'lcm' ) :
                dust_max = value( sect, 'lcm' ) / 10.0
            if dust_max > 999.0 :
                dust_max = 999.0;
        prod_work = ( 1.0 + 5.0 + 10.0 ) * dust_max;

    elif des == 'a' :
        fert = value( sect, 'fert' )
        if fert > 0.0:
            tech = nation_value( 'tech' )
            pe = ( tech + 10.0 ) / ( tech + 20.0 );
            prod_work = 999.0 * 100.0 / ( 9.0 * fert * pe )

    ## other sector types do not produce anything
    result = 0
    if prod_work > 0.0 :
        ##  compensate for work that is needed to increas efficiency
        ##
        ## we have 3 case depending on the new efficiency
        ##  new eff = 100        : add work for getting to 100 eff
        ##  new eff = 60         : 2 times work for getting 60 eff
        ##  new eff = 60 - 100   : see below

        work_100_eff = work_needed_for_eff( sect, 100 )
        if prod_work > work_100_eff :
            result = prod_work + work_100_eff
        else :
            work_60_eff = work_needed_for_eff( sect, 60 )
            if prod_work / 0.6 < work_60_eff :
                result = 2.0 * work_60_eff
            else :
        ##
        ## how much work is needed for production depends on new eff
        ##
        ## total work neeeded is
        ## total work = "work for prod" / ( new_eff / 100 ) + "work for eff"
        ## with new_eff = old_eff + work / 2
        ##
        ## tot_work = prod_work*100/(tot_work/2 + old_eff) + tot_work/2
        ##
        ##
                old_eff = 100.0 - work_100_eff;
                result = - old_eff + math.sqrt( old_eff * old_eff
                                                + 400.0 * prod_work )
    return result


def civ_needed_for_prod( sect ) :
    """ civ needed to produce as much as possible

    returns zero or a negative value if there is enough
    mil and uw for production """


    etu        = version_value( 'UpdateTime' )
    o_brate    = version_value( 'o_brate' )
    civ_growth_fact = ( 1.0 + etu * o_brate )
    result = 0

    if new_designation( sect ) == 'e' :

        new_civ = etu + value( sect, 'mil' ) * ( 2.0 + etu / 10.0)
        work_for_60_eff = ( 2.0 * work_needed_for_eff( sect, 60 )
                            - uw_work( sect ) - mil_work( sect ) )

        if new_civ * etu / 100.0 < work_for_60_eff :

            new_civ = math.ceil( math.ceil( work_for_60_eff )
                                 * 100.0 / etu )

##  	result = math.floor( new_civ / civ_growth_fact + 1.0 )
        result = -math.floor( - new_civ / civ_growth_fact )

    else :
        civ_work_needed = ( work_needed_for_prod( sect )
                            - uw_work( sect ) - mil_work( sect ) )

        civ_work_fact = civ_growth_fact * etu / 100.0
##  	print civ_work_needed
##  	print civ_work_fact
##  	result = math.floor( civ_work_needed  / civ_work_fact + 1.0 )
        result = -math.floor( - civ_work_needed  / civ_work_fact )

    return result



def uw_needed_for_prod( sect ) :
    """ uw needed to produce as much as possible

    returns zero or a negative value if there is enough
    mil and civ for production """

    etu        = version_value( 'UpdateTime' )
    uw_brate   = version_value( 'uw_brate' )

    uw_work_needed = 0.0

    if new_designation( sect ) == 'e' :
        if civ_new( sect ) > 2 * value( sect, 'mil' ) :
            uw_work_needed = ( 2.0 * work_needed_for_eff( sect, 60 )
                               - uw_work( sect ) - mil_work( sect ) )
        else :
            uw_work_needed = - uw_work( sect ) - mil_work( sect )
    else :
        uw_work_needed = ( work_needed_for_prod( sect )
                           - civ_work( sect ) - mil_work( sect ) )

    uw_work_fact = ( 1.0 + etu * uw_brate ) * etu / 100.0
##      return  math.floor( uw_work_needed  / uw_work_fact + 1.0 )
    return  -math.floor( - uw_work_needed / uw_work_fact )




def version_value( what ) :
    """ read some game specific data """
    result = 0
    versionDB = empDb.megaDB['version']
    if what == 'UpdateTime' :
        result = versionDB['updateETUs']
    elif what == 'eat_rate' :
        result = versionDB['eatRate']
    elif what == 'baby_eat' :
        result = versionDB['BEatRate']
    elif what == 'uw_brate' :
        result = versionDB['UBirthRate']
    elif what == 'o_brate' :
        result = versionDB['birthRate']
    return result

def nation_value( what ) :
    """ read nation levels  """
    result = 0
    nationDB = empDb.megaDB['nation']
    if what == 'tech' :
        result = nationDB['technology']
    elif what == 'edu' :
        result = nationDB['education']
    return result

def sectorPredictions(ldb):
    """Return a string containing the sector predictions for LDB."""
    versionDB = empDb.megaDB['version']
    s = ""

    # Population growth predictions
    civs = ldb.get('civ', 0)
    uws = ldb.get('uw', 0)

    newcivs = civ_new(ldb)
    newuws = uw_new(ldb)
    popstr = ""
    if newcivs != civs:
        popstr = "%d civs" % newcivs
    if newuws != uws:
        if popstr:
            popstr = popstr + ", "
        popstr = popstr + "%d uws" % newuws
    food = food_needed_for_breed(ldb)
    if food:
        s = s + " Eats %d" % food
        if popstr:
            s = s + " becoming %s" % popstr
        s = s + ".\n"
        diff = food - ldb.get('food', 0)
        if diff > 0:
            s = s + " NEEDS %d MORE FOOD FOR FULL GROWTH!\n" % diff
    elif popstr:
        s = s + " Expands to %s.\n" % popstr

    # New efficiency:
    sdes = ldb.get('sdes', '_')
    eff = ldb.get('eff', 100)
    if sdes != '_' or eff < 100:
        neweff, newdes = eff_new(ldb)
        try:
            newdes = empParse.sectorDesignationConvert[newdes]
        except KeyError:
            pass
        else:
            s = s + " Builds to a %d%% %s.\n" % (neweff, newdes)
            civ_for_100_eff = civ_needed_for_eff( ldb, 100 ) - civs
            if civ_for_100_eff > 0 :
               s = s + ( " Needs %d more civs to become 100%%.\n"
                         % civ_for_100_eff )
    # Extras
    estr = ""
    des = ldb.get('sdes', '')
    newdes = sdes == '_' and des or sdes
    max_civs = empDb.megaDB['nation']['maxCiv']
    max_uws = empDb.megaDB['nation']['maxUW']

    if newdes == '*' or newdes == '!' or newdes == 'h' :
        # as much available workforce ( = 'avail' ) as possible for
        # harbours, airports and headquarters.
        civ_limit = max_civs
        uw_limit = max_uws
    else:
        civ_limit = civ_needed_for_prod(ldb)
        if civ_limit > max_civs: civ_limit = max_civs
        elif civ_limit < 0: civ_limit = 0

        uw_limit = uw_needed_for_prod(ldb)
        if uw_limit > max_uws: uw_limit = max_uws
        elif uw_limit < 0: uw_limit = 0

        civ_limit = civs - civ_limit
        uw_limit = uws - uw_limit

    if civ_limit > 0:
        s = s + " %d civs not working for production.\n" % civ_limit
    elif civ_limit < 0:
        s = s + " %d civs needed for max production.\n" % -civ_limit
    if uw_limit > 0:
        s = s + " %d uws not working for production.\n" % uw_limit
    elif uw_limit < 0:
        s = s + " %d uws needed for max production.\n" % -uw_limit

    if s:
        s = "\nPredictions:\n" + s
    return s
