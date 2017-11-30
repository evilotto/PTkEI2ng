"""Module that provides virtual options database support for Tk."""

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

def getOptions(root, options, windows):
    db = {}
    for i in windows:
        winopts = {}
        db[i] = winopts
        for j in options:
            val = root.option_get(i+'_'+j, '')
            if val == "\\ ":
                winopts[j] = ""
            elif val != "":
                winopts[j] = val
    return db

def setTextOptions(textWin, names):
    vals = getOptions(textWin,
                      ('background', 'bgstipple', 'borderwidth',
                       'fgstipple', 'font', 'foreground', 'justify',
                       'lmargin1', 'lmargin2', 'offset', 'overstrike',
                       'relief', 'rmargin', 'spacing1', 'spacing2',
                       'spacing3', 'tabs', 'underline', 'wrap'),
                      names)
    for i, j in vals.items():
        apply(textWin.tag_configure, (i,), j)

def getOption(root, name, group, options):
    winopts = {}
    for j in options:
        val = root.option_get(name+'_'+j, group+'_'+j)
        if val == "\\ ":
            winopts[j] = ""
        elif val != "":
            winopts[j] = val
##  	else:
##  	    val = root.option_get(group+'_'+j, '')
##  	    if val == "\\ ":
##  		winopts[j] = ""
##  	    elif val != "":
##  		winopts[j] = val
    return winopts

canvasTypes = {
    'arc': ('extent', 'fill', 'start', 'stipple',
            'style', 'outline', 'outlinestipple'),
    'bitmap': ('anchor', 'background', 'bitmap', 'foreground'),
    'image': ('anchor', 'image'),
    'line': ('arrow', 'arrowshape', 'capstyle', 'fill',
             'joinstyle', 'smooth', 'stipple', 'splinesteps',
             'width'),
    'oval': ('fill', 'outline', 'stipple', 'width'),
    'polygon': ('fill', 'outline', 'smooth', 'splinesteps',
                'stipple', 'width'),
    'rectangle': ('fill', 'outline', 'stipple', 'width'),
    'text': ('anchor', 'fill', 'font', 'justify',
             'stipple', 'text', 'width'),
##      'window': ('anchor', 'height', 'width', 'window'),
    }

def getCanvasObject(canvasWin, name, group):
    try:
        dict = getOption(canvasWin, name, group, ('type', 'coords'))
        type = dict['type']
        coords = tuple(map(float, string.split(dict['coords'])))
        options = getOption(canvasWin, name, group, canvasTypes[type])
        return (getattr(canvasWin, "create_"+type), coords, options)
    except (ValueError, KeyError):
        return None
