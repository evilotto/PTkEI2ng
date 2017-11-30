"""Enhancement to built-in Tk Listbox."""

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

###########################################################################
#############################  My Listbox     #############################
class MyListbox(Tkinter.Listbox):
    """Ughh..  The standard Tk Listbox is essentially useless in its
    current form.  This is an attempt to add at least some functionality."""
    def __init__(self, master=None, cnf={}, **kw):
        defset = {'exportselection':0} #, 'takefocus':0}
        cnf.update(kw)
        self.cmd1 = cnf.get('command')
        if self.cmd1 is not None:
            del cnf['command']
        defset.update(cnf)
        Tkinter.Listbox.__init__(self, master, defset)
        if self.cmd1 is not None:
            btags = self.bindtags()
            self.bindtags((btags[1], btags[0]) + btags[2:])
            self.bind('<Button>', self.do1)
            self.bind('<Motion>', self.do1)
            self.bind('<Key>', self.do1)
        self.datalist = []
        self.curselect = ()
    def curselection(self):
        cs = Tkinter.Listbox.curselection(self)
        return map(operator.getitem, len(cs)*[self.datalist],
                   map(int, cs))
    def get(self, first, last=None):
        pf = self.index(first)
        if last is None:
            pl = pf
        else:
            pl = self.index(last)
        return self.datalist[pf:pl+1]
    def delete(self, items=None):
        """Remove all items from the sequence ITEMS."""
        if items is None:
            # Special case - delete all
            self.datalist = []
            self.curselect = ()
            Tkinter.Listbox.delete(self, 0, 'end')
            self.do1()
            return
        for i in items:
##	    try: j = self.datalist.index(i)
##	    except ValueError: pass
            j = self.datalist.index(i)

            if 0: pass
            else:
                Tkinter.Listbox.delete(self, j)
                del self.datalist[j:j+1]
        self.do1()
    def insert(self, index, *elements):
        pos = self.index(index)
        elmts = []
        for i in elements:
            elmts.append(i[0])
            self.datalist[pos:pos] = [ i[1] ]
            pos = pos + 1
        apply(Tkinter.Listbox.insert, (self, index) + tuple(elmts))
        self.do1()
    def getStatus(self):
        """Return the current selection."""
        act = self.index('active')
        if act:
            act = self.datalist[act]
        return (self.curselection(), act)
    def setStatus(self, loc, act=None):
        self.select_clear(0, 'end')
        for i in loc:
            try: j = self.datalist.index(i)
            except ValueError: pass
            else: self.select_set(j)
        if act:
            try: j = self.datalist.index(act)
            except ValueError: pass
            else: self.activate(j)
        try: self.see(j)
        except NameError: self.select_set(0)
        self.do1()
    def do1(self, event=None):
        cs = Tkinter.Listbox.curselection(self)
        if cs != self.curselect:
            self.curselect = cs
            self.cmd1(self.curselection())
