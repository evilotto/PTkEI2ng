#    Copyright (C) 1998 Ulf Larsson

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
import empDb
import empSector
import math


move_directions = "ujnbgy"
move_reverse_directions ="bgyujn"

def norm_coords( coords, world_size ) :
    """ normalize coordinates according to world size"""
    x , y  = coords
    size_x, size_y  = world_size
    return ( ( x + size_x / 2 ) % size_x - size_x / 2,
             ( y + size_y / 2 ) % size_y - size_y / 2  )


def neighbours( coords ) :
    """ neighbours ordered as directions """
    world = empDb.megaDB['version']['worldsize']
    x , y  = coords

    return  [ norm_coords( ( x + 1, y - 1) , world ) ,
              norm_coords( ( x + 2, y    ) , world ) ,
              norm_coords( ( x + 1, y + 1) , world ) ,
              norm_coords( ( x - 1, y + 1) , world ) ,
              norm_coords( ( x - 2, y    ) , world ) ,
              norm_coords( ( x - 1, y - 1) , world ) ]



def coords_to_str( coords ) :
    x , y  = coords
    return `x` + ',' + `y`

##  MobCost is used in the bestpath algorithm.
##  Bestpath for navigating, marching and
##  exploring needs their own version of
##  this class

class MobCost:
    """ Mobility cost using the move cmd """
    def __init__( self ) :
        pass

    def cost( self, coords ) :
        """ cost for moving into sector """
        result = 2.0 * empSector.infinite_mob_cost
        sect = empDb.megaDB['SECTOR'].get( coords , {} )

        if sect and sect.get( 'owner' ) == empDb.CN_OWNED :
            result = empSector.mob_cost( sect )
        return result

class ExplMobCost:
    """ Mobility cost using the expl cmd """
    def __init__( self ) :
        pass

    def cost( self, coords ) :
        """ cost for moving into sector """
        result = 2.0 * empSector.infinite_mob_cost
        sect = empDb.megaDB['SECTOR'].get( coords, {} )

        if sect and ( sect.get( 'owner' ) == empDb.CN_OWNED
                      or empSector.is_explorable_into( sect ) ) :
            result = empSector.mob_cost( sect )
        return result



##  Path is used in bestpath calculation to keep track of
##  start point, end point , path string and path cost.
##  These are public members right now but should be
##  private.

class Path :
    """ Empire path between sectors in a hex map """
    def __init__( self, sect, mob_cost ) :
        self.start = sect
        self.end = sect
        self.directions = ""
        self.cost = mob_cost

    def append( self, tail, dir ) :
        """ concatinate two paths """
        result = Path( self.start, self.cost + tail.cost )
        result.directions = self.directions + dir + tail.directions
        result.end = tail.end
        return result

    def post_extend( self, sect , mob_cost , dir ) :
        """ add a step at the end of the path """
        result = Path( self.start, self.cost + mob_cost )
        result.directions = self.directions + dir
        result.end = sect
        return result

    def pre_extend( self, sect , mob_cost , dir ) :
        """ add a step at the beginning of the path """
        result = Path( sect, self.cost + mob_cost )
        result.directions = dir + self.directions
        result.end = self.end;
        return result



##  Paths -- bestpath generator between sets of sectors.
##
##
##  Paths has the following data members
##  __mob :      mobility cost object
##  __visited :  dictonary of sector we have calculated a path to
##  __heads :    list of paths starting at a source sector
##  __tails :    list of paths endinging at a destination sector
##  __complete : list of paths starting at a source sector
##               and ends at a destination sector.
##
##  __heads, __tails and __complete are sorted wrt the path cost
##
##  Paths has two main parts. One is to build up paths
##  and the second part deals with removing a source or
##  destination sector.
##
##  Building up paths is done by taking the best head ( or tail) path
##  and create new paths to the neighbours of the path's end point.
##  If the neigbouring sector is *not* in __visited we add the new
##  path, otherwise we try to create a __complete path. This ends
##  when the total cost of the best head and tail path is higher
##  then the best complete path.
##
##  Removing source or destination sector is done by looping through
##  __visited sectors and remove those origin from the removed sector.
##  Same for the lists of paths.
##
##

class Paths :
    """ Paths between two sets of sectors """
    def __init__( self, from_sect, to_sect, mcost ):
        self.__mob = mcost
        self.__visited = {}
        self.__starting_at = {}
        self.__ending_at = {}
        self.__heads = []
        self.__tails = []
        self.__complete = []

        for sect in from_sect:
            path = Path( sect, 0.0 )
            self.__visited[ path.start ] = ( path , 1 )
            self.__starting_at[ path.start ] = [ path ]
            self.__insert_path( self.__heads , path )

        for sect in to_sect :
            path = Path( sect, self.__mob.cost( sect ) )
            self.__visited[ path.end ] = ( path , 0 )
            self.__ending_at[ path.end ] = [ path ]

            self.__insert_path( self.__tails , path )

        self.__make_paths()

    def empty( self ) :
        """ no path exits """
        return ( len( self.__complete ) == 0
                 or self.__complete[ 0 ].cost >= empSector.infinite_mob_cost )

    def best( self ) :
        """ the best path ( lowest cost ) between any two sectors """
        return self.__complete[ 0 ]

    def __found_best_path( self ) :
        """ have we found the best path """
        done_search =  not self.__heads  or  not self.__tails
        if not done_search :
            best_so_far = empSector.infinite_mob_cost

            if self.__complete :
                best_so_far = self.__complete[ 0 ].cost

            best_possible = self.__heads[ 0 ].cost + self.__tails[ 0 ].cost
            done_search = best_possible > best_so_far
        return done_search

    def __insert_path( self, path_list, path ) :
        """ insert path in a sorted list """
        index = 0
        for elem in path_list :
            if path.cost <= elem.cost :
                break
            else :
                index = index + 1;
        path_list.insert( index, path )


    def __make_paths( self ):
        """ expand tail and head paths """
        expand_heads = not 0
        while not self.__found_best_path():
            if expand_heads:
                self.__expand_heads()
            else :
                self.__expand_tails()
            expand_heads = not expand_heads

    def __expand_heads( self ) :
        """ expand best head path """
        path = self.__heads[ 0 ];
#        print "expand head path " + path_str( path )
        del self.__heads[ 0 ]
        i = 0
        for sect in neighbours( path.end ) :
            dir = move_directions[ i ]
            if not self.__visited.has_key( sect ) :
                new_path = path.post_extend( sect ,
                                             self.__mob.cost( sect ),
                                             dir )
                self.__insert_path( self.__heads, new_path )
                self.__visited[ sect ] = ( new_path, 1 )
                self.__starting_at[ path.start ].append( new_path )
            else :
                tail, is_head_path  = self.__visited[ sect ]
                if not is_head_path :
                    self.__insert_path( self.__complete,
                                        path.append( tail, dir ) )
            i = i + 1


    def __expand_tails( self ) :
        """ expand best tail path """

        path = self.__tails[ 0 ]
#        print "expand tail path " + path_str( path ) 
        del self.__tails[ 0 ]

        i = 0
        for sect in neighbours( path.start ) :
            dir = move_reverse_directions[ i ]
            if not self.__visited.has_key( sect ) :
                new_path = path.pre_extend( sect,
                                            self.__mob.cost( sect ),
                                            dir )
                self.__insert_path( self.__tails, new_path )
                self.__visited[ sect ] = ( new_path , 0 )
                self.__ending_at[ path.end ].append( new_path )
            else :
                head, is_head_path  = self.__visited[ sect ]
                if is_head_path :
                    self.__insert_path( self.__complete,
                                        head.append( path, dir ) )
            i = i + 1



## code below deals with removing sectors

    def remove_from( self, coords ) :
        """ remove a sector from the set of source sectors """

        removed = []
        for path in self.__starting_at[ coords ] :
            del self.__visited[ path.end ]
            removed.append( path.end )
        del self.__starting_at[ coords ]
        self.__heads = self.__not_starting_at( self.__heads,
                                               coords )

        self.__complete = self.__not_starting_at( self.__complete,
                                                  coords )
        self.__activate_neighbours_of( removed )
        self.__make_paths()


    def remove_to( self, coords ) :
        """ remove a sector from the set of destination sectors """

        removed = []
        for path in self.__ending_at[ coords ] :
            del self.__visited[ path.start ]
            removed.append( path.start )
        del self.__ending_at[ coords ]
        self.__tails = self.__not_ending_at( self.__tails,
                                             coords )
        self.__complete = self.__not_ending_at( self.__complete,
                                                coords )
        self.__activate_neighbours_of( removed )
        self.__make_paths()

    def __not_starting_at( self,
                           path_list,
                           coords ) :
        """ filter out path not starting at coords """
        result = []
        for path in path_list :
            if path.start != coords  :
                result.append( path )
        return result

    def __not_ending_at( self,
                         path_list,
                         coords ) :
        """ filter out path not starting at coords """
        result = []
        for path in path_list :
            if path.end != coords  :
                result.append( path )
        return result


    def __activate_neighbours_of( self, removed_list ) :
        """ enable neighbouring paths to expand into unvisited sectors """
        for removed in removed_list :
            ## print "activate " + removed.str() + " neighbours"
            for sect in neighbours( removed ) :
                if self.__visited.has_key( sect) :
                     self.__activate_path_end( sect )

    def __activate_path_end( self, sect ) :
        """ insert path to head_paths or tail_paths """
        path , is_head_path = self.__visited[ sect ];
        if is_head_path :
            if path not in self.__heads :
#                print "activate head path " + path_str( path ) 
                self.__insert_path( self.__heads, path )
        else :
            if path not in self.__tails :
#                print "activate tail path " + path_str( path ) 
                self.__insert_path( self.__tails, path )



## only used in debug printing
def path_str( path ) :
    """ make a  string out of a path """
    return ( coords_to_str( path.start ) + ' ' + path.directions
             + ' ' + coords_to_str( path.end )
             + ' (' + `path.cost` + ')' )



## MultiMove use two dictonaries to keep track of mobility
## and amount of commodities in source and destination sectors.
## Paths is used to calculate the best path. For each of these
## paths we check wether we shall remove a source sector or
## a destination sector in the Paths object depending on how
## much we can move.



def best_path( src, dst, mob_cost = MobCost() ) :
    result = None
    paths = Paths( [ src ], [ dst ], mob_cost )
    if not paths.empty() :
        result = paths.best()
    return result



class MoveGenerator :
    """ generator of moves  """
    def __init__( self,
                  commodity,
                  src_secs,
                  dst_secs,
                  mcost = MobCost() ) :

        self.__from_map  = src_secs
        self.__to_map    = dst_secs
        self.__move      = None
        self.__commodity = commodity

        ## print len( src_secs ) , " source sectors",
        ## print len( dst_secs ) , " destination sectors",

        self.__paths = Paths( self.__from_map.keys(),
                              self.__to_map.keys(),
                              mcost )

        ## print "use ", len( self.__from_map ) , " source sectors",
        ## print len( self.__to_map ) , " destination sectors",

        self.next()

    def empty( self ) :
        """ no more move commands """
        return not self.__move

    def next( self ) :
        """ proceede to next move command """
        self.__move = None
        while not ( self.__paths.empty() or self.__move ) :
            path = self.__paths.best()
            ## print "best path = " + path_str( path )
            amount, mob , weight  = self.__from_map[ path.start ]
            if weight * path.cost < mob :
                ## print amount, mob, weight
                move_amount = math.floor( mob / ( weight * path.cost ) )
                if move_amount > amount : move_amount = amount

                to_amount = self.__to_map[ path.end ]
                if move_amount > to_amount : move_amount = to_amount

                amount    = amount - move_amount;
                to_amount = to_amount - move_amount;

                mob = math.floor( mob - weight * path.cost * move_amount )
                self.__move = ( self.__commodity,
                                path,
                                move_amount )

                if to_amount > 0 :
                    self.__to_map[ path.end ] = to_amount
                else :
                    self.__paths.remove_to( path.end )

                if amount > 0 and mob > 0 :
                    self.__from_map[ path.start ] = ( amount ,
                                                      mob ,
                                                      weight)
                else :
                    self.__paths.remove_from( path.start )
            else :
                self.__paths.remove_from( path.start )




    def move( self ) :
        """ current move command """
        return self.__move


class MultiMove :
    """ generator of move commands """
    def __init__( self,
                  commodity,
                  from_secs,
                  from_amount,
                  mob_limit,
                  to_secs,
                  to_amount ) :

        ## print len( from_secs ) , " source sectors",
        ## print len( to_secs ) , " destination sectors",

        if from_amount < 0 : from_amount = 0
        if mob_limit   < 0 : mob_limit   = 0
        if to_amount   < 0 : to_amount   = 0

        src = self.__create_src_map( commodity,
                                     from_secs,
                                     from_amount,
                                     mob_limit )

        dst = self.__create_dst_map( commodity,
                                     to_secs,
                                     to_amount )


        for coords in dst.keys() :
            if src.has_key( coords ) :
                del src[ coords ]

        self.__mover = MoveGenerator( commodity,
                                      src,
                                      dst,
                                      MobCost() )


    def empty( self ) :
        """ no more move commands """
        return self.__mover.empty()

    def next( self ) :
        """ proceede to next move command """
        self.__mover.next()

    def move_cmd_str( self ) :
        """ construct a move command string """
        result = ""
        if not self.__mover.empty() :
            commodity, path, amount = self.__mover.move();
            result = ( 'move ' + commodity + ' '
                       + coords_to_str( path.start ) + ' ' + `amount`
                       + ' ' + coords_to_str( path.end ) )
        return result


    def __create_src_map( self, commodity, from_secs, from_amount, mob_limit ):
        """ create  source sectors dictionary """
        result = {}
        for sect in from_secs.values() :
            coords  = empSector.to_coord( sect )
            if empSector.is_movable_from( sect, commodity ) :

                mob    = empSector.value( sect, 'mob' ) - mob_limit;
                amount = empSector.value( sect, commodity  ) - from_amount

                if  mob > 0 and amount > 0  :
                    weight = empSector.move_weight( sect, commodity )
                    result[ coords ] = ( amount , mob , weight)

                    ## print "src += " + coords.str() + " " + `amount` + " ",
                    ## print `mob` + " " + `weight`
        return result

    def __create_dst_map( self, commodity, to_secs, to_amount ):
        """ create  destination sectors dictionary """
        result =  {}
        for sect in to_secs.values() :
            coords = empSector.to_coord( sect )
            if empSector.is_movable_into( sect, commodity )  :
                amount = to_amount - empSector.value( sect, commodity )
                if  amount > 0  :
                    result[ coords ] = amount
                    ## print "dst += " + coords.str() + " " + `amount`
        return result


class MultiExplore :
    """ generator of explore commands """
    def __init__( self,
                  commodity,
                  from_secs,
                  from_amount,
                  mob_limit,
                  to_secs ) :

        if from_amount < 0 : from_amount = 0
        if mob_limit   < 0 : mob_limit   = 0

        src = self.__create_src_map( commodity,
                                     from_secs,
                                     from_amount,
                                     mob_limit )

        dst = self.__create_dst_map( to_secs )
        self.__explore = MoveGenerator( commodity,
                                        src,
                                        dst,
                                        ExplMobCost() )




    def empty( self ) :
        """ no more explore commands """
        return self.__explore.empty()

    def next( self ) :
        """ proceede to next explore command """
        self.__explore.next()

    def explore_cmd_str( self ) :
        """ construct a expl command string """
        result = ""
        if not self.__explore.empty() :
            commodity, path, amount = self.__explore.move();
            result = ( 'expl ' + commodity + ' '
                       + coords_to_str( path.start ) + ' ' + `amount`
                       + ' ' + path.directions + 'h' )
            return result


    def __create_src_map( self, commodity, from_secs, from_amount, mob_limit ):
        """ init source sectors dictionary """
        result = {};
        for sect in from_secs.values() :
            coords  = empSector.to_coord( sect )
            if empSector.is_movable_from( sect, commodity ) :

                mob    = empSector.value( sect, 'mob' ) - mob_limit;
                amount = empSector.value( sect, commodity ) - from_amount

                if mob > 0 and amount > 0 :
                    weight = 1.0
                    result[ coords ] = ( amount ,
                                         mob ,
                                         weight)
                    ## print "src += " + coords.str() + " " + `amount` + " ",
                    ## print `mob` + " " + `weight`
        return result;


    def __create_dst_map( self, to_secs ):
        """ init destination sectors dictionary """
        result = {}
        for sect in to_secs.values() :
            if empSector.is_explorable_into( sect ) :
                coords = empSector.to_coord( sect )
                result[ coords ] = 1
        return result

