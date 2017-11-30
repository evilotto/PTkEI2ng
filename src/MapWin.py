"""Maintains graphical map window display."""

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

import Tkinter
import string
import operator
import math

import Tk_VDB

import empDb
import empSector
import empPath
import empParse
import empCmd

###########################################################################
#############################  Map window     #############################
class mapSubWin:
    """Maintain map display"""

    def __init__(self, master):
        self.maxCoord = empDb.megaDB['version']['worldsize']
        self.origin = (self.maxCoord[0]/2, self.maxCoord[1]/2)
        self.cursor = self.start = ()
        self.dimen = []

        scrollX = Tkinter.Scrollbar(master, name="scrollX",
                                    orient='horizontal')
        scrollX.grid(row=1, sticky='wes')
        scrollY = Tkinter.Scrollbar(master, name="scrollY",
                                    orient='vertical')
        scrollY.grid(column=1, row=0, sticky='nse')
        self.Map = Tkinter.Canvas(master, name="sectors",
                                  xscrollcommand=scrollX.set,
                                  yscrollcommand=scrollY.set)
        self.Map.grid(column=0, row=0, sticky='nwes')
        scrollX['command'] = self.Map.xview
        scrollY['command'] = self.Map.yview

        master.rowconfigure(0, weight=1)
        master.columnconfigure(0, weight=1)

        self.Map.bind('<ButtonRelease>', self.DoCoordEndBox, "+")
        self.Map.bind('<Enter>', self.DoCoord)
        self.Map.bind('<Motion>', self.DoCoord)
        self.Map.bind('<Leave>', self.DoCoordClear)

        self.Map.bind('<Button-2>', self.DoCoordBox)
        self.Map.bind('<Button2-ButtonRelease>', self.DoSelect)
        self.Map.bind('<Shift-Button-1>', self.DoCoordBox)
        self.Map.bind('<Shift-Button1-ButtonRelease>', self.DoSelect)

        self.Map.bind('<Control-Button-1>',
                      (lambda e, self=self:
                       self.adjustSector(0.90)))
        self.Map.bind('<Control-Button-3>',
                      (lambda e, self=self:
                       self.adjustSector(1.10)))
        self.Map.bind('<Control-Shift-Button-1>',
                      (lambda e, self=self:
                       self.adjustSector(0.50)))
        self.Map.bind('<Control-Shift-Button-3>',
                      (lambda e, self=self:
                       self.adjustSector(2.00)))
        self.Map.bind('<Control-Button-2>',
                      (lambda e, self=self:
                       self.redraw(1)))

        self.Map.bind('<Button-1>', self.DoCensor)
        self.Map.bind('<Button-3>', self.DoOrigin)
        self.Map.bind('<Configure>', self.DoResize)

        # getting Default Mapsize from "TkOption"
        try:
            self.gridsize = map(float, string.split(
                self.Map.option_get("defaultSize", "")))
            self.gridsize[1] = self.gridsize[1] * 3.0/2.0
        except (ValueError, IndexError):
            self.gridsize = [18.0, 24.0]

        # getting default for when to start the Combat Mode, when zooming
        try:
            self.combatModeStartSize = map(float, string.split(
                self.Map.option_get("combatModeStartSize", "")))
            self.combatModeStartSize[1] = self.combatModeStartSize[1] * 3.0/2.0
        except (ValueError, IndexError):
            self.combatModeStartSize = [60.0, 80.0]

        #getting default font for Combat Mode XXX(will be changed in the future)
        try:
            self.combatModeFont = self.Map.option_get("combatModeFont", "")
        except ValueError:
            self.combatModeFont = "courier"

        # activating/deactivating combat mode
        if (self.gridsize[0]>self.combatModeStartSize[0] and
            self.gridsize[1]>self.combatModeStartSize[1]):
                self.combatmode=1
        else:
                self.combatmode=0

        self.optionsDict = {}

        # Register automatic updating
        viewer.updateList.append(self)

        self.redraw(1)

    def adjustSector(self, ratio):
        """Scale the size of the map by RATIO."""
        self.gridsize = map(operator.mul, [ratio]*len(self.gridsize),
                            self.gridsize)
        # activating/deactivating combat mode
        if (self.gridsize[0]>self.combatModeStartSize[0] and
            self.gridsize[1]>self.combatModeStartSize[1]):
                self.combatmode=1
        else:
                self.combatmode=0

        # Redisplay sectors without forcing a redraw.
        xview = self.Map.xview()
        yview = self.Map.yview()
        winWidth = (xview[1] - xview[0])/2.0
        winHeight = (yview[1] - yview[0])/2.0
        ws = self.maxCoord
        self.Map['scrollregion'] = (-self.gridsize[0], -self.gridsize[1],
                                    ws[0]*self.gridsize[0],
                                    ws[1]*self.gridsize[1])
        self.Map.scale('all', 0, 0, ratio, ratio)
        self.Map.xview('moveto', xview[0]+winWidth*(1-1.0/ratio))
        self.Map.yview('moveto', yview[0]+winHeight*(1-1.0/ratio))

    def DoResize(self, event):
        """Tk callback: Note a resize, and adjust the window accordingly."""
        new = (event.width, event.height)
        if not self.dimen:
            # The window is being drawn for the first time
##  	    self.redraw(1)
            self.center()
            self.dimen = new
            return
        xview = self.Map.xview()
        yview = self.Map.yview()
        win = map(float, string.split(self.Map['scrollregion']))
        scrWidth, scrHeight = win[2]-win[0], win[3]-win[1]
        self.Map.xview('moveto', xview[0]
                       +(self.dimen[0]-new[0])/2.0/scrWidth)
        self.Map.yview('moveto', yview[0]
                       +(self.dimen[1]-new[1])/2.0/scrHeight)
        self.dimen = new

    def getCoord(self, coord):
        """Convert empire coords to screen coordinates."""
        return ((coord[0]+self.origin[0])%self.maxCoord[0]*self.gridsize[0],
                (coord[1]+self.origin[1])%self.maxCoord[1]*self.gridsize[1])

    def see(self, coord):
        """If COORD isn't currently viewable, scroll window so that it is."""
        win = map(float, string.split(self.Map['scrollregion']))
        scrWidth, scrHeight = win[2]-win[0], win[3]-win[1]
        xview = self.Map.xview()
        yview = self.Map.yview()
        x, y = self.getCoord(coord)
        xpos, ypos = (x-win[0])/scrWidth, (y-win[1])/scrHeight
        if (xpos < xview[0] or xpos > xview[1]
            or ypos < yview[0] or ypos > yview[1]):
            winWidth = (xview[1] - xview[0])/2.0
            winHeight = (yview[1] - yview[0])/2.0
            self.Map.xview('moveto', xpos - winWidth)
            self.Map.yview('moveto', ypos - winHeight)

    def center(self):
        """Center window."""
        xview = self.Map.xview()
        yview = self.Map.yview()
        winWidth = (xview[1] - xview[0])/2
        winHeight = (yview[1] - yview[0])/2
        self.Map.xview('moveto', 0.5 - winWidth)
        self.Map.yview('moveto', 0.5 - winHeight)

    def setOrigin(self, loc):
        """Change origin to LOC; the origin is the center of the window."""
        # Center window
        self.center()

        # Set origin for future redraws
        loc = (loc[0]-self.maxCoord[0]/2,
               loc[1]-self.maxCoord[1]/2)
        if self.origin == (-loc[0], -loc[1]):
            # Nothing has changed
            return
        x, y = self.getCoord(loc)
        self.origin = (-loc[0], -loc[1])

        # Redisplay sectors without forcing a redraw.
        win = map(float, string.split(self.Map['scrollregion']))
        scrWidth, scrHeight = win[2], win[3]
        self.Map.addtag_enclosed('move_a',
                                 -99999, -99999,
                                 x+1, 99999)
        self.Map.addtag_enclosed('move_b',
                                 x, -99999,
                                 99999, 99999)
        # It is not possible to capture all the x coordinates by drawing a
        # vertical line.  (The x coordinate of every other row is
        # staggered.)  This loop catches these odd starting coordinates.
        for i in (range(y, scrHeight+1, self.gridsize[1])+
                  range(y, -1, -self.gridsize[1])):
            self.Map.addtag_enclosed('move_b',
                                     x-self.gridsize[0],
                                     i-self.gridsize[1]*2/3,
                                     x+self.gridsize[0]+1,
                                     i+self.gridsize[1]*2/3+1)
        self.Map.dtag('move_b', 'move_a')
        self.Map.move('move_a', scrWidth-x, 0)
        self.Map.move('move_b', -x, 0)
        self.Map.dtag('move_a')
        self.Map.dtag('move_b')
        self.Map.addtag_enclosed('move_a',
                                 -99999, -99999,
                                 99999, y-self.gridsize[1]/3+1)
        self.Map.addtag_enclosed('move_b',
                                 -99999, y-self.gridsize[1]*2/3,
                                 99999, 99999)
        self.Map.move('move_a', 0, scrHeight-y)
        self.Map.move('move_b', 0, -y)
        self.Map.dtag('move_a')
        self.Map.dtag('move_b')

    def redraw(self, total=0):
        """DB update handler:  Redraw the window."""
        megaDB = empDb.megaDB
        updateDB = empDb.updateDB

        if total or updateDB['version'].has_key('worldsize'):
            ws = self.maxCoord = megaDB['version']['worldsize']
            self.Map['scrollregion'] = (-self.gridsize[0], -self.gridsize[1],
                                        ws[0]*self.gridsize[0],
                                        ws[1]*self.gridsize[1])
            self.Map.delete('outline')
            self.Map.create_rectangle(-self.gridsize[0], -self.gridsize[1],
                                      ws[0]*self.gridsize[0]-1,
                                      ws[1]*self.gridsize[1]-1,
                                      tags='outline')
            self.origin = (ws[0]/2, ws[1]/2)
            self.center()
            total = 1

        CN_OWNED = empDb.CN_OWNED
        CN_ENEMY = empDb.CN_ENEMY
        CN_UNOWNED = empDb.CN_UNOWNED

        if total:
            db = megaDB['SECTOR']
            self.Map.delete('SECTOR')
        else:
            db = updateDB['SECTOR']
        for i, j in db.items():
            des = j.get('des')
            if not des:
                continue
            own = j.get('owner')
            oldown = j.get('oldown')
            # color for oldownermarks if any shall be drawn
            oldownName="";
            x, y = self.getCoord(i)
            if not total:
                # Delete old sector
                group = self.Map.find_enclosed(x-self.gridsize[0],
                                               y-self.gridsize[1],
                                               x+self.gridsize[0]+1,
                                               y+self.gridsize[1]+1)
                for i in group:
                    if "SECTOR" in self.Map.gettags(i):
                        self.Map.delete(i)
            if own == CN_OWNED:
                mob = j.get('mob')
                if mob is None or mob <= 0:
                    hexName = "nomobSector"
                else:
                    hexName = "ownedSector"
                if oldown is not None and oldown != own:
                    oldownName="oldownerEnemy"
            elif own is not None and (own == CN_ENEMY or own > 0):
                hexName = "enemySector"
                if oldown is not None and oldown != own:
                        if oldown == CN_OWNED:
                                oldownName="oldownerMyself"
                        else:
                                oldownName="oldownerUnknown"
            elif own == CN_UNOWNED:
                hexName = "unownedSector"
            elif des in ".\\":
                hexName = "seaSector"
            elif des == 'X':
                hexName = "mineSector"
            else:
                hexName = "unknownSector"

            sdes = j.get('sdes', '_')
            if sdes != '_':
                des = des + sdes

            # draw hex around sector
            self.Map.lower(self.drawItem(x, y, hexName, "Sector", tags='SECTOR'))
            # Draw text description
            self.drawItem(x, y, hexName+"Text", "SectorText",
                          tags='SECTOR', text=des)

            # Draw a small circle if oldowner!=owner
            if oldownName:
                self.drawItem(x, y, oldownName, "Oldowner", tags='SECTOR')

        # 0,0 axis decoration
        if total:
            x, y = self.getCoord((0,0))
            self.Map.delete("origin")
            self.drawItem(x, y, "origin", "Decoration", tags="origin")
        else:
            self.Map.lift("origin")

        # Capital decoration
        if total or updateDB['nation'].has_key('capital'):
            coord = megaDB['nation']['capital']
            self.Map.delete("capital")
            if coord:
                x, y = self.getCoord(coord)
                self.drawItem(x, y, "capital", "Decoration", tags="capital")
        else:
            self.Map.lift("capital")

        # display infos about units, ships, planes and nukes
        for dbname, tagName, ownedInfo, enemyInfo in (
            ('LAND UNITS', "LAND", "landUnits", "enemyLandUnits"),
            ('SHIPS', "SHIP", "ships", "enemyShips"),
            ('PLANES', "PLANE", "planes", "enemyPlanes"),
            ('NUKES', "NUKE", "nukes", "enemyNukes")):
            if not total and not updateDB[dbname]:
                # No objects in this database have been updated.
                self.Map.lift(ownedInfo)
                self.Map.lift(enemyInfo)
                continue
#	    print "Dealing with " + dbname +":",
            db = megaDB.get(dbname, {})
            self.Map.delete(tagName)
            for i in db.getSec(('x', 'y')).values():
                nu={}
                allUnits=i.values()
                if allUnits:
                    x, y = self.getCoord((allUnits[0]['x'],
                                          allUnits[0]['y']))
                for j in allUnits:
                    owner = j.get('owner')
                    id    = j.get('id')
                    type  = j.get('type')
#		    print "#" + str(id), type,
                    key=()
                    if owner == CN_OWNED:
                        key=CN_OWNED
                    elif owner != CN_UNOWNED:
                        key=CN_ENEMY

                    if key:
                        if nu.has_key(key):
                                nu[key]=nu[key]+1
                        else: nu[key]=1
                        if self.combatmode:
                            self.displayUnit(x,y,nu[key]-1,0.07,
                                             key,id,type,tagName)
                else:
                    if not nu:
                        # No units here.
                        continue
                if nu.has_key(CN_OWNED):
                    self.drawItem(x, y, ownedInfo, "Unit",
                                  tags=tagName)
                if nu.has_key(CN_ENEMY):
                    self.drawItem(x, y, enemyInfo, "EnemyUnit",
                                  tags=tagName)

    def displayUnit(self, x,y, number, scale, owner, id, type, tagName):
        """Display one (additional) Land Unit/Ship/Plane/Nuke for Combat Mode"""

        # Get the start position and color, depending on owner and tagName
        # XXX This is a hack until a configuration method can be added
        if owner==empDb.CN_OWNED:
                textcolor='Black'
        else:
                textcolor='SaddleBrown'

        offset={"LAND":(.433 ,-.483),"SHIP":(-.233 ,-.533),
                "PLANE":(-.233,.133),"NUKE":(.433,.133)}
        nx=offset[tagName][0] + 0
        ny=offset[tagName][1] + scale*number
        # find coords to start
        coords = (nx,ny)
        # Convert the internal coords to screen locations
        l = len(coords)/2
        coords = map(operator.add, (x, y)*l, map(
            operator.mul, self.gridsize*l, coords))

#	print "*g*"
        self.Map.create_text(coords[0],coords[1], tags=tagName,
                             text="#" + str(id) + " " + type ,
                             anchor="nw",
                             font=self.combatModeFont,
                             fill=textcolor)

    def drawItem(self, x, y, name, group, **kw):
        # Get the item
        try:
            item = self.optionsDict[name]
        except KeyError:
            item = self.optionsDict[name] = Tk_VDB.getCanvasObject(
                self.Map, name, group)
##  	    print "Item", name, item
        if item is None:
            # Item known to be invalid
            return
        # Convert the internal coords to screen locations
        coords = item[1]
        l = len(coords)/2
        coords = map(operator.add, (x, y)*l, map(
            operator.mul, (self.gridsize[0], self.gridsize[1]*2.0/3.0)*l,
            coords))
        dict = {}
        dict.update(item[2])
        dict.update(kw)
        # Draw it
        return apply(item[0], tuple(coords), dict)

    def drawPath(self, *coords, **kw):
        """Draw the bestpath between a set of sectors."""
        if coords:
            opts = {'tags':'path', 'smooth':1, 'arrow':'last', 'width':3}
            opts.update(kw)
            coords = map(self.getCoord, coords)
            apply(self.Map.create_line, tuple(coords), opts)
        else:
            self.Map.delete('path')

    def markSectors(self, coords, name="mark"):
        """Mark the specified COORDS with a small circle."""
        self.Map.delete(name)
        for coord in coords:
            x, y = self.getCoord(tuple(coord))
            self.drawItem(x, y, name, "Mark", tags=name)

    def DoCoord(self, event):
        """Tk callback: Mouse has moved; update the current-sector box."""
        # convert screen coords to empire coordinates
        x, y = self.ploc = [
            self.Map.canvasx(event.x)/self.gridsize[0]+0.5,
            self.Map.canvasy(event.y)/self.gridsize[1]+0.5]

        if self.start:
            # Set box to contain the coordinates in proper order
            if x > self.start[0]:
                box = [self.start[0], x]
            else:
                box = [x, self.start[0]]
            if y > self.start[1]:
                box = box + [self.start[1], y]
            else:
                box = box + [y, self.start[1]]
        else:
            box = [x, x, y, y]

        odd_origin = self.origin[0] ^ self.origin[1]
        floor = math.floor

        # Fix bogus ranges
        if floor(box[2]) == floor(box[3]):
            odd_row = (int(floor(box[2])) ^ odd_origin) & 1
            if floor(box[0]) == floor(box[1]):
                box[0] = box[1] = floor((x-0.5+(odd_row^1))/2)*2+odd_row
            else:
                box[0] = floor((box[0]+(odd_row^1))/2)*2+odd_row
                box[1] = floor((box[1]-1+(odd_row^1))/2)*2+odd_row
        if floor(box[0]) == floor(box[1]):
            odd_col = (int(floor(box[0])) ^ odd_origin) & 1
            box[2] = box[2]+((int(floor(box[2]))&1)^odd_col)
            box[3] = box[3]-((int(floor(box[3]))&1)^odd_col)

        box = map(int, map(floor, box))

        # Compensate for the origin
        for box_pos, coord in [[0, 0], [1, 0], [2, 1], [3, 1]]:
            box[box_pos] = ((box[box_pos]-self.origin[coord]
                             +self.maxCoord[coord]/2)
                            %self.maxCoord[coord]-self.maxCoord[coord]/2)

        # Set st to contain a string representation of box
        if box[2] == box[3]:
            st = ",%d" % (box[2],)
        else:
            st = ",%d:%d" % tuple(box[2:])
        if box[0] == box[1]:
            st = "%d" % (box[0],) + st
        else:
            st = "%d:%d" % tuple(box[:2]) + st

        if box == self.cursor:
            # Nothing has changed
            return
        self.cursor = box

        # Display new entry in coord box
        viewer.coord.set(st)

        # redraw box
        self.Map.delete('rubberbox')
        if self.start:
            x1, y1 = self.getCoord((box[0], box[2]))
            x2, y2 = self.getCoord((box[1], box[3]))
            self.CoordBox = self.Map.create_rectangle(
                x1 - self.gridsize[0]/2,
                y1 - self.gridsize[1]/2,
                x2 + self.gridsize[0]/2,
                y2 + self.gridsize[1]/2,
                tags='rubberbox')

    def DoCoordClear(self, event):
        """Tk callback: Clear a range selection."""
        if self.start:
            # When a box is "stretched" beyond the window boundaries a
            # dummy leave event is generated - just ignore it.
            return
        self.cursor = self.start = ()
        viewer.coord.set("")
        self.Map.delete('rubberbox')

    def DoCoordBox(self, event):
        """Tk callback: Start a box for range selection."""
        if self.start:
            # If a button press occurs while "stretching" a box around
            # sectors, cancel all buttons.  (This allows the user to
            # cancel a bad range.)
            self.start = self.cursor = ()
        else:
            self.cursor = ()
            self.start = self.ploc
        self.DoCoord(event)

    def DoCoordEndBox(self, event):
        """Tk callback: End a range selection."""
        self.start = self.cursor = ()
        self.DoCoord(event)

    def DoCensor(self, event):
        """Tk callback: Set the censor window's current sector."""
        if self.start:
            # If the client is selecting a range, just interrupt it and quit.
            self.start = self.cursor = ()
            self.DoCoord(event)
            return
        viewer.cen.SetSect(self.cursor)
        self.DoCoordEndBox(event)

    def DoOrigin(self, event):
        """Tk callback: Center the map window around the current sector."""
        if self.start:
            # If the client is selecting a range, just interrupt it and quit.
            self.start = self.cursor = ()
            self.DoCoord(event)
            return
        self.setOrigin((self.cursor[0], self.cursor[2]))

    def DoSelect(self, event):
        """Tk callback: Insert a sector/range into the command-line."""
        if not self.start:
            return
        rng = viewer.coord.get()
        viewer.insertText(rng)
        self.DoCoordEndBox(event)

##      def DoPopup(self, event):
##          if self.start:
##              # If the client is selecting a range, just interrupt it and quit.
##              self.start = self.cursor = ()
##              self.DoCoord(event)
##              return
##  	menu = Tkinter.Menu(self.Map, name="OptionsMenu")
##  	for i in (
##  	    ("Center", (lambda e, s=self.center: s())),
##  	    ("Move", (lambda e, )))
##  	menu.add_command()


class CmdMap(empCmd.baseCommand):
    description = "Open additional map window."

    defaultBinding = (('Map', 3),)

    def invoke(self):
        self.Root = root = Tkinter.Toplevel(class_="Map")
        root.title("Empire map")
        root.iconname("Empire map")

        # Forward key events to main window.
        viewer.transferKeys(root)

        self.Map = mapSubWin(root)
        viewer.mapList.append(self.Map)

        root.protocol('WM_DELETE_WINDOW', self.handleDelete)

    def handleDelete(self):
        """Tk callback: Remove the window from the display."""
        viewer.updateList.remove(self.Map)
        viewer.mapList.remove(self.Map)
        self.Root.destroy()

class CmdBestpath(empCmd.baseCommand):
    description = "Display a graphical best path."

    sendRefresh = "e"
    defaultBinding = (('Bestpath', 4),)

    def receive(self):
        args = self.commandMatch.group('args')
        if not args:
            coords = ()
        else:
            try:
                coords = map(empParse.str2Coords, string.split(args))
            except ValueError:
                viewer.Error("Bad coords.")
            pos = []
            start = coords[0]
            pos.append(coords[0])
            for i in range(1, len(coords)):
                path = empPath.best_path(coords[i-1], coords[i])
                if path is None:
                    viewer.Error("Path could not be completed.")
                    return
                for i in path.directions:
                    start = empDb.directionToSector(start, i)
                    pos.append(start)
            coords = pos

        apply(viewer.map.drawPath, tuple(coords))

###########################################################################
############################# Map major modes #############################

class MoveMode:
    def __init__(self, mapClass, commodity, source, quantity=None, dest=None):
        self.map = mapClass
        self.Map = mapClass.Map

        # HACK! Test if already in a major mode.
        if self.Map.master.grid_size()[1] > 2:
            viewer.Root.bell()
            return

        # Set up the display area.
        self.Area = Tkinter.Frame(mapClass.Map.master, name="modeInfo")
        self.Area.grid(row=2, sticky="swe")
        self.lblVar = Tkinter.StringVar()
        label = Tkinter.Label(self.Area, name="label", anchor='w',
                              justify='left', textvariable=self.lblVar)
        label.pack(anchor='w')
        self.Quantity = Tkinter.StringVar()
        self.Quantity.trace_variable("w",
                                     (lambda var, o, mode, self=self:
                                      self.redraw()))
        entry = Tkinter.Entry(self.Area, name="quantity",
                              textvariable=self.Quantity)
        entry.pack(anchor='w')
        entry.bind('<Key-Return>', self.DoOk)
        entry.bind('<Key-Escape>', self.finish)
        entry.focus()
        self.okB = Tkinter.Button(self.Area, name="ok", text="Ok",
                                  command=self.DoOk)
        self.okB.pack(side='left', expand=1, fill='x')
        self.cancelB = Tkinter.Button(self.Area, name="cancel", text="Cancel",
                                      command=self.finish)
        self.cancelB.pack(side='right', expand=1, fill='x')

        # Set new bindings for the map window.
        self.oldBindings = []
        for action, command in (
            ('<Button-3>', self.CreateSpot),
            ('<Button3-Motion>', self.MoveSpot),
            ('<Double-Button-3>', self.DelSpot),
            ('<ButtonRelease-3>', self.SetSpot)):
            self.oldBindings.append((action, self.Map.bind(action)))
            self.Map.bind(action, command)

        # Initialize variables
        self.commodity = commodity
        self.source = source
        self.sectors = []
        self.pathList = []
        self.flags = 0

        if quantity is not None:
            self.Quantity.set(quantity)

        self.lblVar.set("")
        self.AddSpot(source)
        if dest is not None:
            self.AddSpot(dest)

        # Register automatic updating
        viewer.updateList.append(self)

    def finish(self, event=None):
        """Unmap the window, and reset the mouse bindings."""
        self.Area.destroy()
        self.map.drawPath()
        self.Map.delete("MoveSector")
        for action, command in self.oldBindings:
            self.Map.tk.call("bind", self.Map, action, command)
        viewer.Prompt.focus()
        viewer.updateList.remove(self)

    def DoOk(self, event=None):
        scts = ""
        for i in self.sectors:
            scts = scts + (" %d,%d" % i)
        viewer.ioq.Send("rdbPe;Mover %s %s%s;rdbe" % (
            self.commodity, self.Quantity.get(), scts))
        self.finish()

    def getSpot(self, coord):
        x, y = self.map.getCoord(coord)
        group = self.Map.find_enclosed(x-self.map.gridsize[0],
                                       y-self.map.gridsize[1],
                                       x+self.map.gridsize[0]+1,
                                       y+self.map.gridsize[1]+1)
        for i in group:
            if "MoveSector" in self.Map.gettags(i):
                return i

    def AddSpot(self, coord, pos=None):
        if pos is None:
            pos = len(self.sectors)
        self.sectors[pos:pos] = [coord]
        x, y = self.map.getCoord(coord)
        self.map.drawItem(x, y, "destSector", "MoveSector",
                            tag="MoveSector")
        self.redraw()

    def CreateSpot(self, event):
        loc = (self.map.cursor[0], self.map.cursor[2])
        if loc in self.sectors:
            # Moving a known spot
            self.pos = self.sectors.index(loc)
        else:
            # See if location is in the current path
            for i in range(len(self.pathList)):
                if loc in self.pathList[i]:
                    self.pos = i+1
                    break
            else:
                # Add spot to end of path
                self.pos = len(self.sectors)
            self.AddSpot(loc, self.pos)
##  	self.start = (event.x, event.y)
        self.start = self.map.getCoord(loc)
        self.spot = self.getSpot(loc)

    def MoveSpot(self, event):
        self.map.DoCoord(event)
        loc = (self.Map.canvasx(event.x), self.Map.canvasy(event.y))
        self.Map.move(self.spot, loc[0]-self.start[0], loc[1]-self.start[1])
        self.start = loc

    def DelSpot(self, event):
        if self.pos is None:
            return
        del self.sectors[self.pos]
        self.Map.delete(self.spot)
        self.redraw()
        self.pos = None

    def SetSpot(self, event):
        if self.pos is None:
            return
##  	del self.sectors[self.pos]
##  	self.Map.delete(self.spot)
        coord = (self.map.cursor[0], self.map.cursor[2])
        newlist = list(self.sectors)
        del newlist[self.pos]
        if coord in newlist:
            self.DelSpot(event)
        else:
            self.sectors[self.pos] = coord
            loc = self.map.getCoord(coord)
            self.Map.move(self.spot, loc[0]-self.start[0],
                          loc[1]-self.start[1])
            self.redraw()

    def redraw(self, total=1):
        if not total and not empDb.updateDB.has_key('SECTOR'):
            # Nothing changed.
            return

        # Remove any existing path.
        self.map.drawPath()

        sectors = self.sectors
        if len(sectors) < 2:
            self.lblVar.set("Select sectors with the right mouse button.\n")
            return
        sDB = empDb.megaDB['SECTOR']
        try:
            quantity = empCmd.getMoveQuantity(self.Quantity.get(),
                                              self.commodity, sectors)
        except ValueError:
            msg = "Enter a valid quantity.\n"
            self.pathList = []
            quantity = 0
        else:
            first = sectors[0]
            last = sectors[-1]
            msg = "Move %d %s: (%d,%d has %s)  (%d,%d has %s)\n" % (
                quantity, self.commodity,
                first[0], first[1], sDB[first].get(self.commodity, "??"),
                last[0], last[1], sDB[last].get(self.commodity, "??"))

        reverse = quantity < 0
        if reverse:
            sectors = list(sectors)
            sectors.reverse()
            quantity = -quantity

        start = sectors[0]
        sectorList = [start]
        newPathList = []
        for i in range(1, len(sectors)):
            last = sectors[i-1]
            path = empPath.best_path(last, sectors[i])
            color = "black"

            newPathList.append([last])
            if path is None:
                # No path between the two sectors.
                color = "red"
                start = sectors[i]
                newPathList[-1].append(start)
                newmob = "??"
##  		return
            else:
                # Calculate new mobility.
                db = sDB[last]
                newmob = int(math.floor(
                    (db.get('mob', 0)
                     - empSector.move_weight(db, self.commodity)
                     * path.cost*quantity)))
                if newmob < 0:
                    color = "yellow"

                # Turn path into list of sector coordinates.
                for i in path.directions:
                    start = empDb.directionToSector(start, i)
                    sectorList.append(start)
                    newPathList[-1].append(start)

            # Update text description.
            msg = msg + "%d,%d=>%s    " % (last[0], last[1], newmob)

            # Draw path
            apply(self.map.drawPath, tuple(newPathList[-1]), {"fill":color})

        if reverse:
            newPathList.reverse()

        self.pathList = newPathList
##  	apply(self.map.drawPath, tuple(sectorList), {"color":color})
        msg = msg + "%d,%d " % sectors[-1]
        self.lblVar.set(msg)
