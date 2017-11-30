"""Maintains graphical censor window."""

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
import types

import Tk_List

import empDb
import empSector

import MapWin

# When listed, units are represented by a tuple: (string, id).  This
# function sorts these tuples.

def compare_tuples(a,b):
    if a[1] < b[1]:
        return -1
    return 1

## def gridClear(win):
##     win['height'] = win.winfo_reqheight()
##     win['width'] = win.winfo_reqwidth()
##     win.grid_propagate(0)
## def packClear(win):
##     def after_f(win=win):
##	h, w = win.winfo_reqheight(), win.winfo_reqwidth()
##	win.pack_propagate(0)
##	win['height'], win['width'] = h, w
##     win.after_idle(after_f)

###########################################################################
#############################  Censor window  #############################
def enterLabel(label):
    label.OldRelief = label['relief']
    label['relief'] = 'groove'
def leaveLabel(label):
    if hasattr(label, 'OldRelief'):
        label['relief'] = label.OldRelief
        del label.OldRelief
##      label['relief'] = 'sunken'
def bindLabel(label):
    label.bind('<Enter>',
               (lambda e, label=label:
                enterLabel(label)))
    label.bind('<Leave>',
               (lambda e, label=label:
                leaveLabel(label)))

class LabPair(Tkinter.Frame):
    """Create a label/value pair for HDL with description LABEL."""
    def __init__(self, master, deflist, name, **kw):
        # label, command, hide, default
        self.name = name
        self.default = kw.get('default')
        self.hide = kw.get('hide')
        label = kw.get('label', string.upper(name[:1]) + name[1:])
        self.label = Tkinter.Label(master, name="label",
                                   text=label, width=7, anchor='ne')
        self.label.pack(side='top', expand=1, fill='both')
        self.value = Tkinter.Label(master, name="value",
##  				   relief='sunken', anchor='ne')
                                   anchor='ne')
        self.value.pack(side='top', expand=1, fill='both')
        try:
            self.value.bind('<Button-1>',
                            (lambda e, c=kw['command'], n=name:
                             c(n)))
            bindLabel(self.value)
        except KeyError: pass
        self.value.bind('<Control-1>', (lambda e, self=self:
                                        viewer.cen.EditField(self.name)))
        deflist[name] = self.update

    def update(self, val, db):
        if callable(self.default):
            val = self.default(val, db)
        elif val == self.default:
            val = ""
        if ((callable(self.hide) and self.hide(val, db))
            or val == self.hide):
            self.label.pack_forget()
            self.value.pack_forget()
        elif ((callable(self.hide) and self.hide(self.value['text']))
               or self.value['text'] == str(self.hide)):
            self.label.pack(expand=1, fill='both')
            self.value.pack(expand=1, fill='both')
        self.value['text'] = val

class LabPairIdx:
    """Same as LabPair, but take two values and create an x/y index."""
    def __init__(self, master, deflist, name, **kw):
        # takes label, command, hide as possible parameters:
        self.default = kw.get('default')
        self.hide = kw.get('hide')
        label = kw.get('label', string.upper(name[:1]) + name[1:])
        self.coord = ["", ""]
        self.label = Tkinter.Label(master, name="label",
                      text=label, width=7, anchor='ne')
        self.value = Tkinter.Label(master, name="value",
##  			   width=4, relief='sunken', anchor='ne')
                           width=4, anchor='ne')
        self.label.pack(side='top', expand=1, fill='both')
        self.value.pack(side='top', expand=1, fill='both')
        if kw.get('command') is not None:
            self.value.bind('<Button-1>',
                            (lambda e, c=kw['command'], n=name:
                             c(n)))
            bindLabel(self.value)
        self.value.bind('<3>', self.goSect)
        deflist[name+"x"] = (lambda val, db, self=self:
                             self.update(0, val, db))
        deflist[name+"y"] = (lambda val, db, self=self:
                             self.update(1, val, db))

    def update(self, pos, val, db):
        self.coord[pos] = val
        val = "%s,%s" % (self.coord[0], self.coord[1])
        if callable(self.default):
            val = self.default(val, db)
        elif val == self.default or val == ",":
            val = ""
        if ((callable(self.hide) and self.hide(val, db))
            or val == self.hide):
            self.label.pack_forget()
            self.value.pack_forget()
        elif ((callable(self.hide) and self.hide(self.value['text']))
               or self.value['text'] == str(self.hide)):
            self.label.pack(expand=1, fill='both')
            self.value.pack(expand=1, fill='both')
        self.value['text'] = val

    def goSect(self, event):
        try:
            x, y = self.coord
            viewer.cen.SetSect((x, x, y, y))
        except ValueError:
            pass

def update(win, val, db):
    """Update a commodity attribute label."""
    if val == 0 or val == '.':
        val = ""
    win['text'] = val

class ComdQuad:
    """Create 4 fields for a commodity."""
    def __init__(self, master, deflist, comd,
                 vhdl=None, dhdl=None, chdl=None, ahdl=None):
        frame = Tkinter.Frame(master, name=comd, class_="Commodity")
        frame.pack(side='top')
        f = comd[0]
        label = Tkinter.Label(frame, name="label",
                              text=string.upper(f)+comd[1:],
                              width=4, anchor='ne')
        label.pack(side='left')
        for i in ((comd, 4, vhdl, 'value'),
                  (f+"_dist", 4, dhdl, 'thresh'),
                  (f+"_cut", 4, chdl, 'cutoff'),
                  (f+"_del", 1, ahdl, 'deliver')):
            tmp = Tkinter.Label(frame, name=i[3], width=i[1],
                                relief='sunken', anchor='ne')
            tmp.pack(side='left')
            if i[2]:
                tmp.bind('<Button-1>', i[2])
                bindLabel(tmp)
            deflist[i[0]] = (lambda val, db, u=update, t=tmp:
                             u(t, val, db))

def DoWinList(rframe, hookList, lablist):
    """Create a frame of label/value pairs from a list description."""
    printSeperator = 0
    row = col = 0
    for i in lablist:
        if not i:
            # make sure empty rows still take space.
            rframe.grid_rowconfigure(row, minsize='1c')
            row = row + 1
            printSeperator = 0
            continue
        if printSeperator:
            Tkinter.Frame(rframe, borderwidth=2, relief='raised', height=2
                          ).grid(row=row, column=0, columnspan=5,
                                 sticky='we')
            row = row + 1
        for j in i:
            if j:
                if j[0] is LabPairIdx: name=j[1]+"sect"
                else: name=j[1]
                tmp = Tkinter.Frame(rframe, name=name, class_="Resources")
##		tmp = Tkinter.Frame(rframe, class_="Resources")
                tmp.grid(column=col, row=row)
                if type(j[-1]) == types.DictType:
                    apply(j[0], (tmp, hookList)+j[1:-1], j[-1])
                else:
                    apply(j[0], (tmp, hookList)+j[1:])
##		packClear(tmp)
            col = col + 1
        row = row + 1
        col = 0
        printSeperator = 1

def translateOwner(val, db):
    """Given an owner id, return a name/id."""
    if val == empDb.CN_OWNED:
        return ""
    return empDb.megaDB['countries'].getName(val)[:7]

def translateDist(val, db):
    """Return a dist sector if it differs from the current sector."""
    if val == ",":
        return ""
    sect = "%s,%s" % (db.get('x'), db.get('y'))
    if val == sect:
        return ""
    return val

class cenWin:
    """Censor Window"""

    class SectorCensus:
        """Subwindow in the censor window that displays sector resources."""
        def __init__(self, master):
            self.key = (0, 0)
            self.db = 'SECTOR'
            self.name = 'sector'

            # Sector resources
            rframe = Tkinter.Frame(master, name="resources", class_="SubCensor")
            rframe.pack(side='top')

            self.Rlist = {}

            # x y des sdes eff mob * off min gold fert ocontent uran work
            # avail terr civ mil uw food shell gun pet iron dust bar oil
            # lcm hcm rad u_del f_del s_del g_del p_del i_del d_del b_del
            # o_del l_del h_del r_del u_cut f_cut s_cut g_cut p_cut i_cut
            # d_cut b_cut o_cut l_cut h_cut r_cut dist_x dist_y c_dist
            # m_dist u_dist f_dist s_dist g_dist p_dist i_dist d_dist
            # b_dist o_dist l_dist h_dist r_dist road rail defense fallout
            # coast c_del m_del c_cut m_cut
            DoWinList(rframe, self.Rlist, (
                ((LabPairIdx, "", {'label':"Sector"}),
                 (LabPair, "owner", {
                     'default':translateOwner,
                     'hide':""}),
                 (LabPair, "oldown", {
                     'label':"OldOwn",
                     'default':(lambda val, db:
                                (val != db.get('owner'))
                                and empDb.megaDB['countries'].getName(val)[:7]
                                or ""),
                     'hide':""}),
                 (LabPair, "sdes", {
                     'label':"NewDes", 'command':self.SetDes,
                     'default':"_", 'hide':""}),
                 (LabPair, "des", {'command':self.SetDes})),

                ((LabPair, "eff"), (LabPair, "mob"),
                 (LabPair, "avail"), (LabPair, "work"),
                 (LabPair, "off", {
                     'label':"Stop", 'default':0,
                     'command': self.toggleStart})),

                ((LabPair, "terr", {'command':self.SetTerr}),
                 (LabPair, "terr1", {'command':self.SetTerr1}),
                 (LabPair, "terr2", {'command':self.SetTerr2}),
                 (LabPair, "terr3", {'command':self.SetTerr3}),
                 (LabPair, "coast")),

                ((LabPair, "min"), (LabPair, "gold"), (LabPair, "fert"),
                 (LabPair, "ocontent", {'label':"Oil"}), (LabPair, "uran")),

                ((LabPair, "road",
                  {'command':
                   (lambda comd, self=self:
                    viewer.queryCommand(
                        "Improve road of sector %s,%s to ?" % self.key,
                        "eval %s,%s improve road [sect] [%%s-road]" % self.key,
                        "rdbe", "rdbPe"))}),
                 (LabPair, "rail",
                  {'command':
                   (lambda comd, self=self:
                    viewer.queryCommand(
                        "Improve rail of sector %s,%s to ?" % self.key,
                        "eval %s,%s improve rail [sect] [%%s-rail]" % self.key,
                        "rdbe", "rdbPe"))}),
                 (LabPair, "defense",
                  {'command':
                   (lambda comd, self=self:
                    viewer.queryCommand(
                        "Improve defense of sector %s,%s to ?" % self.key,
                        "eval %s,%s improve def [sect] [%%s-dfense]" % self.key,
                        "rdbe", "rdbPe"))}),
                 (LabPair, "fallout", {'default':0, 'hide':""}),
                 (LabPairIdx, "dist_",
                      {'label':"Dist",
                       'default':translateDist,
                       'command':self.SetDist})),
                (),
                ))

            self.predictVar = Tkinter.StringVar()
            predict = Tkinter.Label(master, height=1, width=1, anchor='nw',
                                    justify='left', relief='flat',
                                    textvariable=self.predictVar)
            predict.pack(side='bottom', fill='both', expand=1)
            viewer.Balloon.bind(predict, "Guesses about the next update")

            cframe = Tkinter.Frame(master, name="commodities")
            cframe.pack(side='left', anchor='ne')
            lcframe = Tkinter.Frame(cframe, name="label")
            lcframe.pack()
            Tkinter.Label(lcframe, name="label", text="Type",
                  width=4, anchor='w').pack(side='left')
            Tkinter.Label(lcframe, name="value", text="Qty",
                  width=4, anchor='w').pack(side='left')
            Tkinter.Label(lcframe, name="thresh", text="Thr",
                  width=4, anchor='w').pack(side='left')
            Tkinter.Label(lcframe, name="cutoff", text="Del",
                  width=4, anchor='w').pack(side='left')
            Tkinter.Label(lcframe, name="direction",
                  width=1, anchor='w').pack(side='left')
            for i in ("civ", "mil", "uw", "food", "shell", "gun", "pet"):
                ComdQuad(cframe, self.Rlist, i,
                         (lambda e, h=self.SetCurrent, i=i:
                          h(i)),
                         (lambda e, h=self.SetThresh, i=i:
                          h(i)),
                         (lambda e, h=self.SetDel, i=i:
                          h(i)),
                         (lambda e, h=self.SetDir, i=i:
                          h(i)))

            cframe = Tkinter.Frame(master, name="commodities2")
            cframe.pack(side='left', anchor='ne')
            lcframe = Tkinter.Frame(cframe, name="label")
            lcframe.pack()
            Tkinter.Label(lcframe, name="label", text="Type",
                  width=4, anchor='w').pack(side='left')
            Tkinter.Label(lcframe, name="value", text="Qty",
                  width=4, anchor='w').pack(side='left')
            Tkinter.Label(lcframe, name="thresh", text="Thr",
                  width=4, anchor='w').pack(side='left')
            Tkinter.Label(lcframe, name="cutoff", text="Del",
                  width=4, anchor='w').pack(side='left')
            Tkinter.Label(lcframe, name="direction",
                  width=1, anchor='w').pack(side='left')
            for i in ("iron", "dust", "bar", "oil", "lcm", "hcm", "rad"):
                ComdQuad(cframe, self.Rlist, i,
                         (lambda e, h=self.SetCurrent, i=i:
                          h(i)),
                         (lambda e, h=self.SetThresh, i=i:
                          h(i)),
                         (lambda e, h=self.SetDel, i=i:
                          h(i)),
                         (lambda e, h=self.SetDir, i=i:
                          h(i)))

        def SetSect(self, range):
            self.key = (range[0], range[2])
            viewer.markSectors([(range[0], range[2])])
            viewer.map.see((range[0], range[2]))
            self.redraw(1)

        def getKey(self):
            return "%s,%s"%self.key

        def EditField(self, name):
            if viewer.stsList:
                viewer.Root.bell()
                return
            def f(val, db=self.db, key=self.key, name=name):
                if not val:
                    return
                db = empDb.megaDB[db]
                t = {}
                for i in range(len(key)):
                    t[db.primary_keytype[i]] = key[i]
                t[name] = val
                db.update(t)
                viewer.redraw(0)
            viewer.bufferStatus(
                "Manually edit %s value at %s,%s to ?" % ((name,) + self.key),
                f)

        def SetDist(self, name):
            viewer.queryCommand(
                "New dist sector for %s,%s ?" % self.key,
                "dist %s,%s %%s" % self.key,
                "rdbe")

        def SetDes(self, name):
            viewer.queryCommand(
                "New designation for %s,%s ?" % self.key,
                "des %s,%s %%s" % self.key,
                "rdbe")

        def toggleStart(self, name):
            if empDb.megaDB['SECTOR'][self.key].get('off') == 0:
                cmd = "stop"
            else:
                cmd = "start"
            viewer.ioq.Send(cmd + " %s,%s; rdbe" % self.key)

        def SetTerr(self, name):
            viewer.queryCommand(
                "New territory value for %s,%s ?" % self.key,
                "territory %s,%s %%s" % self.key,
                "rdbe")

        def SetTerr1(self, name):
            viewer.queryCommand(
                "New territory value for %s,%s ?" % self.key,
                "territory %s,%s %%s 1" % self.key,
                "rdbe")

        def SetTerr2(self, name):
            viewer.queryCommand(
                "New territory value for %s,%s ?" % self.key,
                "territory %s,%s %%s 2" % self.key,
                "rdbe")

        def SetTerr3(self, name):
            viewer.queryCommand(
                "New territory value for %s,%s ?" % self.key,
                "territory %s,%s %%s 3" % self.key,
                "rdbe")

        def SetCurrent(self, comd):
            DB = empDb.megaDB['SECTOR'][self.key]
            dx = DB.get('dist_x'); dy = DB.get('dist_y')
            if dx is not None and dy is not None and (dx, dy) != self.key:
                dist = (dx, dy)
            else:
                dist = None
            MapWin.MoveMode(viewer.map, comd, self.key, None, dist)
##  	    viewer.queryCommand(
##  		"Resupply %s commodity at %s,%s to?" % ((comd,) + self.key),
##  		(("eval %s,%s move %s [%%s>%s and dist+' '+`%%s-%s`+' '+sect"
##  		  +" or sect+' '+`%s-%%s`+' '+dist]")
##  		 % (self.key + (comd, comd, comd, comd))),
##  		"rdbe", "rdbPe")

        def SetThresh(self, comd):
            viewer.queryCommand(
                "New %s threshold for %s,%s ?" % ((comd,) + self.key),
                "thresh %s %s,%s %%s" % ((comd,) + self.key),
                "rdbe")

        def SetDel(self, comd):
            viewer.queryCommand(
                "New %s cutoff for %s,%s ?" % ((comd,) + self.key),
                "deli %s %s,%s +%%s" % ((comd,) + self.key),
                "rdbe")

        def SetDir(self, comd):
            viewer.queryCommand(
                "New %s direction for %s,%s ?" % ((comd,) + self.key),
                "eval %s,%s deli %s [sect] [%s] %%s" % (
                    self.key + (comd, comd[0]+'_del')),
                "rdbe", "rdbPe")

        def redraw(self, total):
            if not total and not empDb.updateDB[self.db].has_key(self.key):
                # Nothing has been updated
                return
            DB = empDb.megaDB[self.db]
            DBs = DB.get(self.key, {})
            for i, j in self.Rlist.items():
                j(DBs.get(i, ""), DBs)
            self.predictVar.set(empSector.sectorPredictions(DBs))

    class UnitCensus:
        """Generic class that Land/Ship/Plane classes descend from."""
        def doStartup(self, master):
            self.key = 0

            self.sect = ()

            sframe = Tkinter.Frame(master, name=self.name, class_="SubCensor")
            sframe.pack(side='bottom', fill='both', expand=1)
            scrollY = Tkinter.Scrollbar(sframe, name="scrollY")
            scrollY.pack(side='right', fill='y')
            self.List = Tk_List.MyListbox(sframe, name="list",
                                          height=4, command=self.SetId,
                                          yscrollcommand=scrollY.set)
            self.List.pack(side='left', fill='both', expand=1)
            scrollY['command'] = self.List.yview

            rframe = Tkinter.Frame(master, name="resources")
            rframe.pack(side='top')

            self.Rlist = {}

            DoWinList(rframe, self.Rlist, self.winList)

        def redrawWin(self, total=0):
            if not total and not empDb.updateDB[self.db].has_key(self.key):
                # Nothing has been updated
                return
            DB = empDb.megaDB[self.db]
            DBs = DB.get(self.key, {})
            for i, j in self.Rlist.items():
                j(DBs.get(i, ""), DBs)

        def getKey(self):
            return str(self.key[0])

        def SetId(self, info):
            if info: self.key = (info[0],)
            else: self.key = ()
            self.redrawWin(1)

        def SetSect(self, range):
            self.sect = range
            viewer.markSectors([(range[0], range[2])])
            viewer.map.see((range[0], range[2]))
            self.redraw()

        def EditField(self, name):
            if viewer.stsList:
                viewer.Root.bell()
                return
            def f(val, db=self.db, key=self.key, name=name):
                if not val:
                    return
                db = empDb.megaDb[db]
                t = {}
                for i in len(self.key):
                    t[db.primary_keytype[i]] = self.key[i]
                t[name] = val
                db.update(t)
            viewer.bufferStatus(
                "Manually edit %s value of %s to ?" % (name, self.key[0]),
                f)

        def redraw(self, total=0):
            self.redrawWin(total)
            sts = self.List.getStatus()
            DB = empDb.megaDB.get(self.db, {})
            self.List.delete()
            list = []
            for i, j in DB.items():
                if self.sect:
                    x = j['x']; y = j['y']
                    if (x < self.sect[0] or x > self.sect[1]
                        or y < self.sect[2] or y > self.sect[3]):
                        continue
##		if j.get('owner') != empDb.CN_OWNED:
##		    continue
                if j.get('owner') == empDb.CN_UNOWNED:
                    continue
                addi = ""
                if j.get('owner') != empDb.CN_OWNED:
                    addi = "owner:%-3s" % (j.get('owner'),)
                list.append(
                    ("%-3s@ %-8s type: %-3s%10s" %
                     (j['id'], ("%s,%s" % (j['x'], j['y'])),j['type'], addi),
                     j['id']))
            list.sort(compare_tuples)
            for i in list:
                self.List.insert('end', i)
            apply(self.List.setStatus, sts)

        def GoLand(self, name):
            k = empDb.megaDB.get(self.db, {}).get(self.key, {}).get('land')
            if k is None or k == -1:
                return
            viewer.cen.blist['Land'].handle.key = ( k, )
            viewer.cen.newWin(viewer.cen.blist['Land'])

        def GoShip(self, range):
            k = empDb.megaDB.get(self.db, {}).get(self.key, {}).get('ship')
            if k is None or k == -1:
                return
            viewer.cen.blist['Ship'].handle.key = ( k, )
            viewer.cen.newWin(viewer.cen.blist['Ship'])

    class ShipCensus(UnitCensus):
        """Subwindow within the censor window that displays ships."""
        def __init__(self, master):
            self.db = 'SHIPS'
            self.name = 'ship'

            cc = {'command':self.LoadComd}

            # id type x y flt eff civ mil uw food pln he xl land mob fuel tech
            # shell gun petrol iron dust bar oil lcm hcm rad
            # def spd vis rng fir origx origy name
            self.winList = (
                ((LabPair, "id"), (LabPair, "type"),
                 (LabPair, "owner", {'default':translateOwner,
                                     'hide':""}),
                 (LabPairIdx, "", {'label':"Sector", 'command':self.GoSect}),
                 (LabPair, "flt", {'label':"Fleet", 'command':self.SetFleet})),

                ((LabPair, "eff"), (LabPair, "mob"), (LabPair, "fuel"),
                 (LabPair, "tech")),

                ((LabPair, "def"), (LabPair, "spd", {'label':"Speed"}),
                 (LabPair, "vis"), (LabPair, "rng", {'label':"Range"}),
                 (LabPair, "fir")),

                ((LabPair, "pln", {'label':"Planes"}), (LabPair, "land"),
                 (LabPair, "he"), (LabPair, "xl")),

                ((LabPairIdx, "orig"),
                 (LabPair, "name", {'command':self.SetName})),

                (),
                # List of commodities
                ((LabPair, "civ", cc), (LabPair, "mil", cc),
                 (LabPair, "uw", cc), (LabPair, "food", cc),
                 (LabPair, "shell", cc)),
                ((LabPair, "gun", cc), (LabPair, "petrol", cc),
                 (LabPair, "iron", cc), (LabPair, "dust", cc),
                 (LabPair, "bar", cc)),
                ((LabPair, "oil", cc), (LabPair, "lcm", cc),
                 (LabPair, "hcm", cc), (LabPair, "rad", cc)),
                )
            self.doStartup(master)

        def GoSect(self, name):
            viewer.queryCommand(
                "Navigate ship %s to ?" % self.key,
                "navi %s %%s" % self.key,
                "rdbs")

        def SetFleet(self, name):
            viewer.queryCommand(
                "Add ship %s to fleet ?" % self.key,
                "fleet %%s %s" % self.key,
                "rdbs")

        def SetName(self, name):
            viewer.queryCommand(
                "New name for ship %s ?" % self.key,
                'name %s "%%s"' % self.key,
                "rdbs")

        def LoadComd(self, comd):
            viewer.queryCommand(
                "Set %s cargo on ship %s to ?" % (comd, self.key[0]),
                "load %s %s -%%s" % (comd, self.key[0]),
                "rdbes")

    class LandCensus(UnitCensus):
        """Subwindow within the censor window that displays land units."""
        def __init__(self, master):
            self.db = 'LAND UNITS'
            self.name = 'land'

            cc = {'command':self.LoadComd}

            # id type x y army eff mil fort mob food fuel tech retr react xl
            # nland land ship shell gun petrol iron dust bar oil lcm hcm rad
            # att def vul spd vis spy radius frg acc dam amm aaf
            self.winList = (
                ((LabPair, "id"), (LabPair, "type"),
                 (LabPair, "owner", {'default':translateOwner,
                                     'hide':""}),
                 (LabPairIdx, "", {'label':"Sector", 'command':self.GoSect}),
                 (LabPair, "army", {'command':self.SetArmy})),

                ((LabPair, "eff"), (LabPair, "mob"), (LabPair, "fuel"),
                 (LabPair, "tech")),

                ((LabPair, "fort"), (LabPair, "retr"),
                 (LabPair, "react", {'command':self.SetRange}),
                 (LabPair, "att"), (LabPair, "def")),

                ((LabPair, "vul"), (LabPair, "spd"),
                 (LabPair, "vis"), (LabPair, "spy"),
                 (LabPair, "radius")),

                ((LabPair, "frg"), (LabPair, "acc"),
                 (LabPair, "dam"),
                 (LabPair, "amm"), (LabPair, "aaf")),

                ((LabPair, "xl"), (LabPair, "nland"), (),
                 (LabPair, "land", {'default':-1, 'command':self.GoLand}),
                 (LabPair, "ship", {'default':-1, 'command':self.GoShip})),

                (),
                # List of commodities
                ((LabPair, "civ", cc), (LabPair, "mil", cc),
                 (LabPair, "uw", cc), (LabPair, "food", cc),
                 (LabPair, "shell", cc)),
                ((LabPair, "gun", cc), (LabPair, "petrol", cc),
                 (LabPair, "iron", cc), (LabPair, "dust", cc),
                 (LabPair, "bar", cc)),
                ((LabPair, "oil", cc), (LabPair, "lcm", cc),
                 (LabPair, "hcm", cc), (LabPair, "rad", cc)),
                )
            self.doStartup(master)

        def GoSect(self, name):
            viewer.queryCommand(
                "March land unit %s to ?" % self.key,
                "march %s %%s" % self.key,
                "rdbl")

        def SetArmy(self, name):
            viewer.queryCommand(
                "Add land unit %s to army ?" % self.key,
                "army %%s %s" % self.key,
                "rdbl")

        def SetRange(self, name):
            viewer.queryCommand(
                "Set reaction range of land unit %s to ?" % self.key,
                "lrange %s %%s" % self.key,
                "rdbl")

        def LoadComd(self, comd):
            viewer.queryCommand(
                "Set %s cargo on land unit %s to ?" % (comd, self.key[0]),
                "lload %s %s -%%s" % (comd, self.key[0]),
                "rdbel")

    class PlaneCensus(UnitCensus):
        """Subwindow within the censor window that displays planes."""
        def __init__(self, master):
            self.db = 'PLANES'
            self.name = 'plane'

            # id type x y wing eff mob tech att def acc react range load
            # fuel hard ship land laun orb nuke grd
            self.winList = (
                ((LabPair, "id"), (LabPair, "type"),
                 (LabPair, "owner", {'default':translateOwner,
                                     'hide':""}),
                 (LabPairIdx, "", {'label':"Sector", 'command':self.GoSect}),
                 (LabPair, "wing", {'command':self.SetWing})),

                ((LabPair, "eff"), (LabPair, "mob"), (LabPair, "fuel"),
                 (LabPair, "tech")),

                ((LabPair, "hard"),
                 (LabPair, "react", {'command':self.SetRange}),
                 (LabPair, "att"), (LabPair, "def")),

                ((LabPair, "acc"), (LabPair, "range"),
                 (LabPair, "load"), (LabPair, "laun"),
                 (LabPair, "orb")),

                ((LabPair, "nuke"), (LabPair, "grd"), (),
                 (LabPair, "land", {'default':-1, 'command':self.GoLand}),
                 (LabPair, "ship", {'default':-1, 'command':self.GoShip})),
                )
            self.doStartup(master)

        def GoSect(self, name):
            viewer.queryCommand(
                "Transport plane %s to ?" % self.key,
                "transp plane %s %%s" % self.key,
                "rdbp")

        def SetWing(self, name):
            viewer.queryCommand(
                "Add plane %s to wing ?" % self.key,
                "wing %%s %s" % self.key,
                "rdbp")

        def SetRange(self, name):
            viewer.queryCommand(
                "Set reaction range of plane %s to ?" % self.key,
                "range %s %%s" % self.key,
                "rdbp")

    ####################
    # Main censor window
    def __init__(self, master):
        self.master = master
        self.blist = {}
        self.sect = (0,0,0,0)

        buttons = Tkinter.Frame(master, name="buttons")
        buttons.pack(side='top', fill='x')
        for i in (#('Nuke', self.SectorCensus, 'NUKES'),
                  ('Plane', self.PlaneCensus, 'PLANES',
                   "View planes"),
                  ('Land', self.LandCensus, 'LAND UNITS',
                   "View land units"),
                  ('Ship', self.ShipCensus, 'SHIPS',
                   "View ships"),
                  ('Sector', self.SectorCensus, 'SECTOR',
                   "View sector information.")):
            frm = Tkinter.Frame(master, name="f"+i[0], class_="Buttons",
                        relief='raised', borderwidth=2)
            frm.handle = i[1](frm)
            frm.db = i[2]
            frm.button = Tkinter.Button(buttons, name="b"+i[0],
                                        text=i[0], relief='flat',
                                        command=(lambda self=self, cls=frm:
                                                 self.newWin(cls)))
            frm.button.pack(side='right', fill='y', expand=1)
            viewer.Balloon.bind(frm.button, i[3])
            self.blist[i[0]] = frm
        self.subWindow = frm
        frm.button['relief'] = 'raised'
        frm.pack(fill='both', expand=1)
        self.SetSect((0,0,0,0))

        # Register automatic updating
        viewer.updateList.append(self)

    def newWin(self, ofType):
        if self.subWindow is not ofType:
            self.subWindow.button['relief'] = 'flat'
            self.subWindow.pack_forget()
            self.subWindow = ofType
            self.subWindow.button['relief'] = 'raised'
            self.subWindow.pack(fill='both', expand=1)
        # Hack! Reset the sectors for units, but not sectors.
        if self.subWindow.handle.__class__ is self.SectorCensus:
            self.subWindow.handle.SetSect(self.sect)
        else:
            self.subWindow.handle.sect = ()
            self.redraw(1)

    def redraw(self, total):
        self.subWindow.handle.redraw(total)

    def getKey(self):
        return self.subWindow.handle.getKey()

    def getSect(self):
        return self.sect

    def SetSect(self, range):
        self.sect = range
        self.subWindow.handle.SetSect(range)

    def EditField(self, field):
        self.subWindow.handle.EditField(field)
