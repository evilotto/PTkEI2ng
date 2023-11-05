

### Loader functions:

_VERSION = 'I2ng'

def setversion(version):
    if version != _VERSION:
        raise ValueError('Dynamic versioning not available')

def setalphaversions(*alpha_versions):
    if alpha_versions != ():
        raise ValueError('Dynamic versioning not available')

def version(alpha = 0):
    if alpha:
        return ()
    else:
        return _VERSION

def installedversions(alpha = 0):
    if alpha:
        return ()
    else:
        return (_VERSION,)


######################################################################
### File: PmwBase.py
# Pmw megawidget base classes.

# This module provides a foundation for building megawidgets.  It
# contains the MegaArchetype class which manages component widgets and
# configuration options.  Also provided are the MegaToplevel and
# MegaWidget classes, derived from the MegaArchetype class.  The
# MegaToplevel class contains a Tkinter Toplevel widget to act as the
# container of the megawidget.  This is used as the base class of all
# megawidgets that are contained in their own top level window, such
# as a Dialog window.  The MegaWidget class contains a Tkinter Frame
# to act as the container of the megawidget.  This is used as the base
# class of all other megawidgets, such as a ComboBox or ButtonBox.
#
# Megawidgets are built by creating a class that inherits from either
# the MegaToplevel or MegaWidget class.

import os
import string
import sys
import traceback
import types
import tkinter
import collections

# tkinter 8.5 -> 8.6 fixed a problem in which selected indexes
# were reported as strings instead of ints
# by default emulate the same functionality so we don't break 
# existing interfaces but allow for easy switching
#_forceTkinter85Compatibility = True

#def setTkinter85Compatible(value):
#    global _forceTkinter85Compatibility
#    if isinstance(value, bool):
#        _forceTkinter85Compatibility = value and tkinter.TkVersion > 8.5
        
#def emulateTk85():
#    global _forceTkinter85Compatibility
#    return _forceTkinter85Compatibility

# Special values used in index() methods of several megawidgets.
END = ['end']
SELECT = ['select']
DEFAULT = ['default']

# Constant used to indicate that an option can only be set by a call
# to the constructor.
INITOPT = ['initopt']
_DEFAULT_OPTION_VALUE = ['default_option_value']
_useTkOptionDb = 0

# Symbolic constants for the indexes into an optionInfo list.
_OPT_DEFAULT         = 0
_OPT_VALUE           = 1
_OPT_FUNCTION        = 2

# Stacks

_busyStack = []
    # Stack which tracks nested calls to show/hidebusycursor (called
    # either directly or from activate()/deactivate()).  Each element
    # is a dictionary containing:
    #   'newBusyWindows' :  List of windows which had busy_hold called
    #                       on them during a call to showbusycursor().
    #                       The corresponding call to hidebusycursor()
    #                       will call busy_release on these windows.
    #   'busyFocus' :       The blt _Busy window which showbusycursor()
    #                       set the focus to.
    #   'previousFocus' :   The focus as it was when showbusycursor()
    #                       was called.  The corresponding call to
    #                       hidebusycursor() will restore this focus if
    #                       the focus has not been changed from busyFocus.

_grabStack = []
    # Stack of grabbed windows.  It tracks calls to push/popgrab()
    # (called either directly or from activate()/deactivate()).  The
    # window on the top of the stack is the window currently with the
    # grab.  Each element is a dictionary containing:
    #   'grabWindow' :      The window grabbed by pushgrab().  The
    #                       corresponding call to popgrab() will release
    #                       the grab on this window and restore the grab
    #                       on the next window in the stack (if there is one).
    #   'globalMode' :      True if the grabWindow was grabbed with a
    #                       global grab, false if the grab was local
    #                       and 'nograb' if no grab was performed.
    #   'previousFocus' :   The focus as it was when pushgrab()
    #                       was called.  The corresponding call to
    #                       popgrab() will restore this focus.
    #   'deactivateFunction' :
    #       The function to call (usually grabWindow.deactivate) if
    #       popgrab() is called (usually from a deactivate() method)
    #       on a window which is not at the top of the stack (that is,
    #       does not have the grab or focus).  For example, if a modal
    #       dialog is deleted by the window manager or deactivated by
    #       a timer.  In this case, all dialogs above and including
    #       this one are deactivated, starting at the top of the
    #       stack.

    # Note that when dealing with focus windows, the name of the Tk
    # widget is used, since it may be the '_Busy' window, which has no
    # python instance associated with it.

#=============================================================================

# Functions used to forward methods from a class to a component.

# Fill in a flattened method resolution dictionary for a class (attributes are
# filtered out). Flattening honours the MI method resolution rules
# (depth-first search of bases in order). The dictionary has method names
# for keys and functions for values.
def __methodDict(cls, dict):

    # the strategy is to traverse the class in the _reverse_ of the normal
    # order, and overwrite any duplicates.
    baseList = list(cls.__bases__)
    baseList.reverse()

    # do bases in reverse order, so first base overrides last base
    for super in baseList:
        __methodDict(super, dict)

    # do my methods last to override base classes
    for key, value in list(cls.__dict__.items()):
        # ignore class attributes
        if type(value) == types.FunctionType:
            dict[key] = value

def __methods(cls):
    # Return all method names for a class.

    # Return all method names for a class (attributes are filtered
    # out).  Base classes are searched recursively.

    dictio = {}
    __methodDict(cls, dictio)
    return list(dictio.keys())

# Function body to resolve a forwarding given the target method name and the
# attribute name. The resulting lambda requires only self, but will forward
# any other parameters.
__stringBody = (
    'def %(method)s(this, *args, **kw): return ' +
    #'apply(this.%(attribute)s.%(method)s, args, kw)')
    'this.%(attribute)s.%(method)s(*args, **kw)');

# Get a unique id
__counter = 0
def __unique():
    global __counter
    __counter = __counter + 1
    return str(__counter)

# Function body to resolve a forwarding given the target method name and the
# index of the resolution function. The resulting lambda requires only self,
# but will forward any other parameters. The target instance is identified
# by invoking the resolution function.
__funcBody = (
    'def %(method)s(this, *args, **kw): return ' +
    #'apply(this.%(forwardFunc)s().%(method)s, args, kw)')
    'this.%(forwardFunc)s().%(method)s(*args, **kw)');

def forwardmethods(fromClass, toClass, toPart, exclude = ()):
    # Forward all methods from one class to another.

    # Forwarders will be created in fromClass to forward method
    # invocations to toClass.  The methods to be forwarded are
    # identified by flattening the interface of toClass, and excluding
    # methods identified in the exclude list.  Methods already defined
    # in fromClass, or special methods with one or more leading or
    # trailing underscores will not be forwarded.

    # For a given object of class fromClass, the corresponding toClass
    # object is identified using toPart.  This can either be a String
    # denoting an attribute of fromClass objects, or a function taking
    # a fromClass object and returning a toClass object.

    # Example:
    #     class MyClass:
    #     ...
    #         def __init__(self):
    #             ...
    #             self.__target = TargetClass()
    #             ...
    #         def findtarget(self):
    #             return self.__target
    #     forwardmethods(MyClass, TargetClass, '__target', ['dangerous1', 'dangerous2'])
    #     # ...or...
    #     forwardmethods(MyClass, TargetClass, MyClass.findtarget,
    #             ['dangerous1', 'dangerous2'])

    # In both cases, all TargetClass methods will be forwarded from
    # MyClass except for dangerous1, dangerous2, special methods like
    # __str__, and pre-existing methods like findtarget.


    # Allow an attribute name (String) or a function to determine the instance
    if not isinstance(toPart, str):

        # check that it is something like a function
        if hasattr(toPart, '__call__'):

            # If a method is passed, use the function within it
            if hasattr(toPart, 'im_func'):
                toPart = toPart.__func__

            # After this is set up, forwarders in this class will use
            # the forwarding function. The forwarding function name is
            # guaranteed to be unique, so that it can't be hidden by subclasses
            forwardName = '__fwdfunc__' + __unique()
            fromClass.__dict__[forwardName] = toPart

        # It's not a valid type
        else:
            raise TypeError('toPart must be attribute name, function or method')

    # get the full set of candidate methods
    dict = {}
    __methodDict(toClass, dict)

    # discard special methods
    for ex in list(dict.keys()):
        if ex[:1] == '_' or ex[-1:] == '_':
            del dict[ex]
    # discard dangerous methods supplied by the caller
    for ex in exclude:
        if ex in dict:
            del dict[ex]
    # discard methods already defined in fromClass
    for ex in __methods(fromClass):
        if ex in dict:
            del dict[ex]

    for method, func in list(dict.items()):
        d = {'method': method, 'func': func}
        if isinstance(toPart, str):
            execString = \
                __stringBody % {'method' : method, 'attribute' : toPart}
        else:
            execString = \
                __funcBody % {'forwardFunc' : forwardName, 'method' : method}

        exec(execString, d)

        # this creates a method
        #fromClass.__dict__[method] = d[method]
        setattr(fromClass, method, d[method])


#=============================================================================

def setgeometryanddeiconify(window, geom):
    # To avoid flashes on X and to position the window correctly on NT
    # (caused by Tk bugs).

    if os.name == 'nt' or \
            (os.name == 'posix' and sys.platform[:6] == 'cygwin'):
        # Require overrideredirect trick to stop window frame
        # appearing momentarily.
        redirect = window.overrideredirect()
        if not redirect:
            window.overrideredirect(1)
        window.deiconify()
        if geom is not None:
            window.geometry(geom)
        # Call update_idletasks to ensure NT moves the window to the
        # correct position it is raised.
        window.update_idletasks()
        window.tkraise()
        if not redirect:
            window.overrideredirect(0)
    else:
        if geom is not None:
            window.geometry(geom)

        # Problem!?  Which way around should the following two calls
        # go?  If deiconify() is called first then I get complaints
        # from people using the enlightenment or sawfish window
        # managers that when a dialog is activated it takes about 2
        # seconds for the contents of the window to appear.  But if
        # tkraise() is called first then I get complaints from people
        # using the twm window manager that when a dialog is activated
        # it appears in the top right corner of the screen and also
        # takes about 2 seconds to appear.

        #window.tkraise()
        # Call update_idletasks to ensure certain window managers (eg:
        # enlightenment and sawfish) do not cause Tk to delay for
        # about two seconds before displaying window.
        #window.update_idletasks()
        #window.deiconify()

        window.deiconify()
        if window.overrideredirect():
            # The window is not under the control of the window manager
            # and so we need to raise it ourselves.
            window.tkraise()

#=============================================================================

class MegaArchetype:
    # Megawidget abstract root class.

    # This class provides methods which are inherited by classes
    # implementing useful bases (this class doesn't provide a
    # container widget inside which the megawidget can be built).

    def __init__(self, parent = None, hullClass = None):

        # Mapping from each megawidget option to a list of information
        # about the option
        #   - default value
        #   - current value
        #   - function to call when the option is initialised in the
        #     call to initialiseoptions() in the constructor or
        #     modified via configure().  If this is INITOPT, the
        #     option is an initialisation option (an option that can
        #     be set by the call to the constructor but can not be
        #     used with configure).
        # This mapping is not initialised here, but in the call to
        # defineoptions() which precedes construction of this base class.
        #
        # self._optionInfo = {}

        # Mapping from each component name to a tuple of information
        # about the component.
        #   - component widget instance
        #   - configure function of widget instance
        #   - the class of the widget (Frame, EntryField, etc)
        #   - cget function of widget instance
        #   - the name of the component group of this component, if any
        self.__componentInfo = {}

        # Mapping from alias names to the names of components or
        # sub-components.
        self.__componentAliases = {}

        # Contains information about the keywords provided to the
        # constructor.  It is a mapping from the keyword to a tuple
        # containing:
        #    - value of keyword
        #    - a boolean indicating if the keyword has been used.
        # A keyword is used if, during the construction of a megawidget,
        #    - it is defined in a call to defineoptions() or addoptions(), or
        #    - it references, by name, a component of the megawidget, or
        #    - it references, by group, at least one component
        # At the end of megawidget construction, a call is made to
        # initialiseoptions() which reports an error if there are
        # unused options given to the constructor.
        #
        # After megawidget construction, the dictionary contains
        # keywords which refer to a dynamic component group, so that
        # these components can be created after megawidget
        # construction and still use the group options given to the
        # constructor.
        #
        # self._constructorKeywords = {}

        # List of dynamic component groups.  If a group is included in
        # this list, then it not an error if a keyword argument for
        # the group is given to the constructor or to configure(), but
        # no components with this group have been created.
        # self._dynamicGroups = ()

        if hullClass is None:
            self._hull = None
        else:
            if parent is None:
                parent = tkinter._default_root

            # Create the hull.
            self._hull = self.createcomponent('hull',
                    (), None,
                    hullClass, (parent,))
            _hullToMegaWidget[self._hull] = self

            if _useTkOptionDb:
                # Now that a widget has been created, query the Tk
                # option database to get the default values for the
                # options which have not been set in the call to the
                # constructor.  This assumes that defineoptions() is
                # called before the __init__().
                option_get = self.option_get
                _VALUE = _OPT_VALUE
                _DEFAULT = _OPT_DEFAULT
                for name, info in list(self._optionInfo.items()):
                    value = info[_VALUE]
                    if value is _DEFAULT_OPTION_VALUE:
                        resourceClass = str.upper(name[0]) + name[1:]
                        value = option_get(name, resourceClass)
                        if value != '':
                            try:
                                # Convert the string to int/float/tuple, etc
                                value = eval(value, {'__builtins__': {}})
                            except:
                                pass
                            info[_VALUE] = value
                        else:
                            info[_VALUE] = info[_DEFAULT]

    def destroy(self):
        # Clean up optionInfo in case it contains circular references
        # in the function field, such as self._settitle in class
        # MegaToplevel.

        self._optionInfo = {}
        if self._hull is not None:
            del _hullToMegaWidget[self._hull]
            self._hull.destroy()

    #======================================================================
    # Methods used (mainly) during the construction of the megawidget.

    def defineoptions(self, keywords, optionDefs, dynamicGroups = ()):
        # Create options, providing the default value and the method
        # to call when the value is changed.  If any option created by
        # base classes has the same name as one in <optionDefs>, the
        # base class's value and function will be overriden.

        # This should be called before the constructor of the base
        # class, so that default values defined in the derived class
        # override those in the base class.

        if not hasattr(self, '_constructorKeywords'):
            # First time defineoptions has been called.
            tmp = {}
            for option, value in list(keywords.items()):
                tmp[option] = [value, 0]
            self._constructorKeywords = tmp
            self._optionInfo = {}
            self._initialiseoptions_counter = 0
        self._initialiseoptions_counter = self._initialiseoptions_counter + 1

        if not hasattr(self, '_dynamicGroups'):
            self._dynamicGroups = ()
        self._dynamicGroups = self._dynamicGroups + tuple(dynamicGroups)
        self.addoptions(optionDefs)

    def addoptions(self, optionDefs):
        # Add additional options, providing the default value and the
        # method to call when the value is changed.  See
        # "defineoptions" for more details

        # optimisations:
        optionInfo = self._optionInfo
        #optionInfo_has_key = optionInfo.has_key
        keywords = self._constructorKeywords
        #keywords_has_key = keywords.has_key
        FUNCTION = _OPT_FUNCTION

        for name, default, function in optionDefs:
            if '_' not in name:
                # The option will already exist if it has been defined
                # in a derived class.  In this case, do not override the
                # default value of the option or the callback function
                # if it is not None.
                if not name in optionInfo:
                    if name in keywords:
                        value = keywords[name][0]
                        optionInfo[name] = [default, value, function]
                        del keywords[name]
                    else:
                        if _useTkOptionDb:
                            optionInfo[name] = \
                                    [default, _DEFAULT_OPTION_VALUE, function]
                        else:
                            optionInfo[name] = [default, default, function]
                elif optionInfo[name][FUNCTION] is None:
                    optionInfo[name][FUNCTION] = function
            else:
                # This option is of the form "component_option".  If this is
                # not already defined in self._constructorKeywords add it.
                # This allows a derived class to override the default value
                # of an option of a component of a base class.
                if not name in keywords:
                    keywords[name] = [default, 0]

    def createcomponent(self, componentName, componentAliases,
            componentGroup, widgetClass, *widgetArgs, **kw):
        #print('inCreateComponent', componentName)
        # Create a component (during construction or later).

        if componentName in self.__componentInfo:
            raise ValueError('Component "%s" already exists' % componentName)

        if '_' in componentName:
            raise ValueError('Component name "%s" must not contain "_"' % componentName)

        if hasattr(self, '_constructorKeywords'):
            keywords = self._constructorKeywords
        else:
            keywords = {}
        for alias, component in componentAliases:
            # Create aliases to the component and its sub-components.
            index = str.find(component, '_')
            if index < 0:
                self.__componentAliases[alias] = (component, None)
            else:
                mainComponent = component[:index]
                subComponent = component[(index + 1):]
                self.__componentAliases[alias] = (mainComponent, subComponent)

            # Remove aliases from the constructor keyword arguments by
            # replacing any keyword arguments that begin with *alias*
            # with corresponding keys beginning with *component*.

            alias = alias + '_'
            aliasLen = len(alias)
            for option in list(keywords.keys()):
                if len(option) > aliasLen and option[:aliasLen] == alias:
                    newkey = component + '_' + option[aliasLen:]
                    keywords[newkey] = keywords[option]
                    del keywords[option]

        componentPrefix = componentName + '_'
        nameLen = len(componentPrefix)
        for option in list(keywords.keys()):
            if len(option) > nameLen and option[:nameLen] == componentPrefix:
                # The keyword argument refers to this component, so add
                # this to the options to use when constructing the widget.
                kw[option[nameLen:]] = keywords[option][0]
                del keywords[option]
            else:
                # Check if this keyword argument refers to the group
                # of this component.  If so, add this to the options
                # to use when constructing the widget.  Mark the
                # keyword argument as being used, but do not remove it
                # since it may be required when creating another
                # component.
                index = str.find(option, '_')
                if index >= 0 and componentGroup == option[:index]:
                    rest = option[(index + 1):]
                    kw[rest] = keywords[option][0]
                    keywords[option][1] = 1

        if 'pyclass' in kw:
            widgetClass = kw['pyclass']
            del kw['pyclass']
        if widgetClass is None:
            return None
        if len(widgetArgs) == 1 and type(widgetArgs[0]) == tuple:
            # Arguments to the constructor can be specified as either
            # multiple trailing arguments to createcomponent() or as a
            # single tuple argument.
            widgetArgs = widgetArgs[0]
        widget = widgetClass(*widgetArgs, **kw)
        componentClass = widget.__class__.__name__
        self.__componentInfo[componentName] = (widget, widget.configure,
                componentClass, widget.cget, componentGroup)

        return widget

    def destroycomponent(self, name):
        # Remove a megawidget component.

        # This command is for use by megawidget designers to destroy a
        # megawidget component.

        self.__componentInfo[name][0].destroy()
        del self.__componentInfo[name]

    def createlabel(self, parent, childCols = 1, childRows = 1):

        labelpos = self['labelpos']
        labelmargin = self['labelmargin']
        if labelpos is None:
            return

        label = self.createcomponent('label',
                (), None,
                tkinter.Label, (parent,))

        if labelpos[0] in 'ns':
            # vertical layout
            if labelpos[0] == 'n':
                row = 0
                margin = 1
            else:
                row = childRows + 3
                margin = row - 1
            label.grid(column=2, row=row, columnspan=childCols, sticky=labelpos)
            parent.grid_rowconfigure(margin, minsize=labelmargin)
        else:
            # horizontal layout
            if labelpos[0] == 'w':
                col = 0
                margin = 1
            else:
                col = childCols + 3
                margin = col - 1
            label.grid(column=col, row=2, rowspan=childRows, sticky=labelpos)
            parent.grid_columnconfigure(margin, minsize=labelmargin)

    def initialiseoptions(self, dummy = None):
        self._initialiseoptions_counter = self._initialiseoptions_counter - 1
        if self._initialiseoptions_counter == 0:
            unusedOptions = []
            keywords = self._constructorKeywords
            for name in list(keywords.keys()):
                used = keywords[name][1]
                if not used:
                    # This keyword argument has not been used.  If it
                    # does not refer to a dynamic group, mark it as
                    # unused.
                    index = str.find(name, '_')
                    if index < 0 or name[:index] not in self._dynamicGroups:
                        unusedOptions.append(name)
            if len(unusedOptions) > 0:
                if len(unusedOptions) == 1:
                    text = 'Unknown option "'
                else:
                    text = 'Unknown options "'
                raise KeyError(text + str.join(unusedOptions, ', ') + \
                        '" for ' + self.__class__.__name__)

            # Call the configuration callback function for every option.
            FUNCTION = _OPT_FUNCTION
            for info in list(self._optionInfo.values()):
                func = info[FUNCTION]
                if func is not None and func is not INITOPT:
                    func()

    #======================================================================
    # Method used to configure the megawidget.

    def configure(self, option=None, **kw):
        # Query or configure the megawidget options.
        #
        # If not empty, *kw* is a dictionary giving new
        # values for some of the options of this megawidget or its
        # components.  For options defined for this megawidget, set
        # the value of the option to the new value and call the
        # configuration callback function, if any.  For options of the
        # form <component>_<option>, where <component> is a component
        # of this megawidget, call the configure method of the
        # component giving it the new value of the option.  The
        # <component> part may be an alias or a component group name.
        #
        # If *option* is None, return all megawidget configuration
        # options and settings.  Options are returned as standard 5
        # element tuples.
        #
        # If *option* is a string, return the 5 element tuple for the
        # given configuration option.

        # First, deal with the option queries.
        if len(kw) == 0:
            # This configure call is querying the values of one or all options.
            # Return 5-tuples:
            #     (optionName, resourceName, resourceClass, default, value)
            if option is None:
                rtn = {}
                for option, config in list(self._optionInfo.items()):
                    resourceClass = str.upper(option[0]) + option[1:]
                    rtn[option] = (option, option, resourceClass,
                            config[_OPT_DEFAULT], config[_OPT_VALUE])
                return rtn
            else:
                config = self._optionInfo[option]
                resourceClass = str.upper(option[0]) + option[1:]
                return (option, option, resourceClass, config[_OPT_DEFAULT],
                        config[_OPT_VALUE])

        # optimisations:
        optionInfo = self._optionInfo
        componentInfo = self.__componentInfo
        componentAliases = self.__componentAliases
        VALUE = _OPT_VALUE
        FUNCTION = _OPT_FUNCTION

        # This will contain a list of options in *kw* which
        # are known to this megawidget.
        directOptions = []

        # This will contain information about the options in
        # *kw* of the form <component>_<option>, where
        # <component> is a component of this megawidget.  It is a
        # dictionary whose keys are the configure method of each
        # component and whose values are a dictionary of options and
        # values for the component.
        indirectOptions = {}

        for option, value in list(kw.items()):
            if option in optionInfo:
                # This is one of the options of this megawidget.
                # Make sure it is not an initialisation option.
                if optionInfo[option][FUNCTION] is INITOPT:
                    raise KeyError(
                            'Cannot configure initialisation option "'
                            + option + '" for ' + self.__class__.__name__)
                optionInfo[option][VALUE] = value
                directOptions.append(option)
            else:
                index = option.find('_')
                if index >= 0:
                    # This option may be of the form <component>_<option>.
                    component = option[:index]
                    componentOption = option[(index + 1):]

                    # Expand component alias
                    if component in componentAliases:
                        component, subComponent = componentAliases[component]
                        if subComponent is not None:
                            componentOption = subComponent + '_' \
                                    + componentOption

                        # Expand option string to write on error
                        option = component + '_' + componentOption

                    if component in componentInfo:
                        # Configure the named component
                        componentConfigFuncs = [componentInfo[component][1]]
                    else:
                        # Check if this is a group name and configure all
                        # components in the group.
                        componentConfigFuncs = []
                        for info in list(componentInfo.values()):
                            if info[4] == component:
                                componentConfigFuncs.append(info[1])

                        if len(componentConfigFuncs) == 0 and \
                                component not in self._dynamicGroups:
                            raise KeyError('Unknown option "' + option +
                                    '" for ' + self.__class__.__name__)

                    # Add the configure method(s) (may be more than
                    # one if this is configuring a component group)
                    # and option/value to dictionary.
                    for componentConfigFunc in componentConfigFuncs:
                        if not componentConfigFunc in indirectOptions:
                            indirectOptions[componentConfigFunc] = {}
                        indirectOptions[componentConfigFunc][componentOption] \
                                = value
                else:
                    raise KeyError('Unknown option "' + option +
                            '" for ' + self.__class__.__name__)

        # Call the configure methods for any components.
        for func, values in indirectOptions.items():
            func(**values);

        # Call the configuration callback function for each option.
        for option in directOptions:
            info = optionInfo[option]
            func = info[_OPT_FUNCTION]
            if func is not None:
                func()

    def __setitem__(self, key, value):
        self.configure(**{key: value})

    #======================================================================
    # Methods used to query the megawidget.

    def component(self, name):
        # Return a component widget of the megawidget given the
        # component's name
        # This allows the user of a megawidget to access and configure
        # widget components directly.

        # Find the main component and any subcomponents
        index = str.find(name, '_')
        if index < 0:
            component = name
            remainingComponents = None
        else:
            component = name[:index]
            remainingComponents = name[(index + 1):]

        # Expand component alias
        if component in self.__componentAliases:
            component, subComponent = self.__componentAliases[component]
            if subComponent is not None:
                if remainingComponents is None:
                    remainingComponents = subComponent
                else:
                    remainingComponents = subComponent + '_' \
                            + remainingComponents

        widget = self.__componentInfo[component][0]
        if remainingComponents is None:
            return widget
        else:
            return widget.component(remainingComponents)

    def interior(self):
        return self._hull

    def hulldestroyed(self):
        return self._hull not in _hullToMegaWidget

    def __str__(self):
        return str(self._hull)

    def cget(self, option):
        # Get current configuration setting.

        # Return the value of an option, for example myWidget['font'].
        if option in self._optionInfo:
            return self._optionInfo[option][_OPT_VALUE]
        else:
            index = str.find(option, '_')
            if index >= 0:
                component = option[:index]
                componentOption = option[(index + 1):]

                # Expand component alias
                if component in self.__componentAliases:
                    component, subComponent = self.__componentAliases[component]
                    if subComponent is not None:
                        componentOption = subComponent + '_' + componentOption

                    # Expand option string to write on error
                    option = component + '_' + componentOption

                if component in self.__componentInfo:
                    # Call cget on the component.
                    componentCget = self.__componentInfo[component][3]
                    return componentCget(componentOption)
                else:
                    # If this is a group name, call cget for one of
                    # the components in the group.
                    for info in list(self.__componentInfo.values()):
                        if info[4] == component:
                            componentCget = info[3]
                            return componentCget(componentOption)

        raise KeyError('Unknown option "' + option + \
                '" for ' + self.__class__.__name__)

    __getitem__ = cget

    def isinitoption(self, option):
        return self._optionInfo[option][_OPT_FUNCTION] is INITOPT

    def options(self):
        options = []
        if hasattr(self, '_optionInfo'):
            for option, info in list(self._optionInfo.items()):
                isinit = info[_OPT_FUNCTION] is INITOPT
                default = info[_OPT_DEFAULT]
                options.append((option, default, isinit))
            options.sort()
        return options

    def components(self):
        # Return a list of all components.

        # This list includes the 'hull' component and all widget subcomponents

        names = list(self.__componentInfo.keys())
        names.sort()
        return names

    def componentaliases(self):
        # Return a list of all component aliases.

        componentAliases = self.__componentAliases

        names = list(componentAliases.keys())
        names.sort()
        rtn = []
        for alias in names:
            (mainComponent, subComponent) = componentAliases[alias]
            if subComponent is None:
                rtn.append((alias, mainComponent))
            else:
                rtn.append((alias, mainComponent + '_' + subComponent))

        return rtn

    def componentgroup(self, name):
        return self.__componentInfo[name][4]

#=============================================================================

# The grab functions are mainly called by the activate() and
# deactivate() methods.
#
# Use pushgrab() to add a new window to the grab stack.  This
# releases the grab by the window currently on top of the stack (if
# there is one) and gives the grab and focus to the new widget.
#
# To remove the grab from the window on top of the grab stack, call
# popgrab().
#
# Use releasegrabs() to release the grab and clear the grab stack.

def pushgrab(grabWindow, globalMode, deactivateFunction):
    prevFocus = grabWindow.tk.call('focus')
    grabInfo = {
        'grabWindow' : grabWindow,
        'globalMode' : globalMode,
        'previousFocus' : prevFocus,
        'deactivateFunction' : deactivateFunction,
    }
    _grabStack.append(grabInfo)
    _grabtop()
    grabWindow.focus_set()

def popgrab(window):
    # Return the grab to the next window in the grab stack, if any.

    # If this window is not at the top of the grab stack, then it has
    # just been deleted by the window manager or deactivated by a
    # timer.  Call the deactivate method for the modal dialog above
    # this one on the stack.
    if _grabStack[-1]['grabWindow'] != window:
        for index in range(len(_grabStack)):
            if _grabStack[index]['grabWindow'] == window:
                _grabStack[index + 1]['deactivateFunction']()
                break

    grabInfo = _grabStack[-1]
    del _grabStack[-1]

    topWidget = grabInfo['grabWindow']
    prevFocus = grabInfo['previousFocus']
    globalMode = grabInfo['globalMode']

    if globalMode != 'nograb':
        topWidget.grab_release()

    if len(_grabStack) > 0:
        _grabtop()
    if prevFocus != '':
        try:
            topWidget.tk.call('focus', prevFocus)
        except tkinter.TclError:
            # Previous focus widget has been deleted. Set focus
            # to root window.
            tkinter._default_root.focus_set()
    else:
        # Make sure that focus does not remain on the released widget.
        if len(_grabStack) > 0:
            topWidget = _grabStack[-1]['grabWindow']
            topWidget.focus_set()
        else:
            tkinter._default_root.focus_set()

def grabstacktopwindow():
    if len(_grabStack) == 0:
        return None
    else:
        return _grabStack[-1]['grabWindow']

def releasegrabs():
    # Release grab and clear the grab stack.

    current = tkinter._default_root.grab_current()
    if current is not None:
        current.grab_release()
    _grabStack[:] = []

def _grabtop():
    grabInfo = _grabStack[-1]
    topWidget = grabInfo['grabWindow']
    globalMode = grabInfo['globalMode']

    if globalMode == 'nograb':
        return

    while 1:
        try:
            if globalMode:
                topWidget.grab_set_global()
            else:
                topWidget.grab_set()
            break
        except tkinter.TclError:
            # Another application has grab.  Keep trying until
            # grab can succeed.
            topWidget.after(100)

#=============================================================================

class MegaToplevel(MegaArchetype):

    def __init__(self, parent = None, **kw):
        # Define the options for this megawidget.
        optiondefs = (
            ('activatecommand',   None,                     None),
            ('deactivatecommand', None,                     None),
            ('master',            None,                     None),
            ('title',             None,                     self._settitle),
            ('hull_class',        self.__class__.__name__,  None),
        )
        self.defineoptions(kw, optiondefs)

        # Initialise the base class (after defining the options).
        super().__init__(parent, tkinter.Toplevel)
        
        # Initialise instance.

        # Set WM_DELETE_WINDOW protocol, deleting any old callback, so
        # memory does not leak.
        if hasattr(self._hull, '_Pmw_WM_DELETE_name'):
            self._hull.tk.deletecommand(self._hull._Pmw_WM_DELETE_name)
        self._hull._Pmw_WM_DELETE_name = \
                self.register(self._userdeletewindow, needcleanup = 0)
        self.protocol('WM_DELETE_WINDOW', self._hull._Pmw_WM_DELETE_name)

        # Initialise instance variables.

        self._firstShowing = 1
        # Used by show() to ensure window retains previous position on screen.

        # The IntVar() variable to wait on during a modal dialog.
        self._wait = None

        self._active = 0
        self._userdeletefunc = self.destroy
        self._usermodaldeletefunc = self.deactivate

        # Check keywords and initialise options.
        self.initialiseoptions()

    def _settitle(self):
        title = self['title']
        if title is not None:
            self.title(title)

    def userdeletefunc(self, func=None):
        if func:
            self._userdeletefunc = func
        else:
            return self._userdeletefunc

    def usermodaldeletefunc(self, func=None):
        if func:
            self._usermodaldeletefunc = func
        else:
            return self._usermodaldeletefunc

    def _userdeletewindow(self):
        if self.active():
            self._usermodaldeletefunc()
        else:
            self._userdeletefunc()

    def destroy(self):
        # Allow this to be called more than once.
        if self._hull in _hullToMegaWidget:
            self.deactivate()

            # Remove circular references, so that object can get cleaned up.
            del self._userdeletefunc
            del self._usermodaldeletefunc

            MegaArchetype.destroy(self)

    def show(self, master = None):
        if self.state() != 'normal':
            if self._firstShowing:
                # Just let the window manager determine the window
                # position for the first time.
                geom = None
            else:
                # Position the window at the same place it was last time.
                geom = self._sameposition()
            setgeometryanddeiconify(self, geom)

        if self._firstShowing:
            self._firstShowing = 0
        else:
            if self.transient() == '':
                self.tkraise()

        # Do this last, otherwise get flashing on NT:
        if master is not None:
            if master == 'parent':
                parent = self.winfo_parent()
                # winfo_parent() should return the parent widget, but the
                # the current version of Tkinter returns a string.
                if type(parent) is str:
                    parent = self._hull._nametowidget(parent)
                master = parent.winfo_toplevel()
            self.transient(master)

        self.focus()

    def _centreonscreen(self):
        # Centre the window on the screen.  (Actually halfway across
        # and one third down.)

        parent = self.winfo_parent()
        if type(parent) is str:
            parent = self._hull._nametowidget(parent)

        # Find size of window.
        self.update_idletasks()
        width = self.winfo_width()
        height = self.winfo_height()
        if width == 1 and height == 1:
            # If the window has not yet been displayed, its size is
            # reported as 1x1, so use requested size.
            width = self.winfo_reqwidth()
            height = self.winfo_reqheight()

        # Place in centre of screen:
        x = (self.winfo_screenwidth() - width) / 2 - parent.winfo_vrootx()
        y = (self.winfo_screenheight() - height) / 3 - parent.winfo_vrooty()
        if x < 0:
            x = 0
        if y < 0:
            y = 0
        return '+%d+%d' % (x, y)

    def _sameposition(self):
        # Position the window at the same place it was last time.

        geometry = self.geometry()
        index = str.find(geometry, '+')
        if index >= 0:
            return geometry[index:]
        else:
            return None

    def activate(self, globalMode = 0, geometry = 'centerscreenfirst'):
        if self._active:
            raise ValueError('Window is already active')
        if self.state() == 'normal':
            self.withdraw()

        self._active = 1

        showbusycursor()

        if self._wait is None:
            self._wait = tkinter.IntVar()
        self._wait.set(0)

        if geometry == 'centerscreenalways':
            geom = self._centreonscreen()
        elif geometry == 'centerscreenfirst':
            if self._firstShowing:
                # Centre the window the first time it is displayed.
                geom = self._centreonscreen()
            else:
                # Position the window at the same place it was last time.
                geom = self._sameposition()
        elif geometry[:5] == 'first':
            if self._firstShowing:
                geom = geometry[5:]
            else:
                # Position the window at the same place it was last time.
                geom = self._sameposition()
        else:
            geom = geometry

        self._firstShowing = 0

        setgeometryanddeiconify(self, geom)

        # Do this last, otherwise get flashing on NT:
        master = self['master']
        if master is not None:
            if master == 'parent':
                parent = self.winfo_parent()
                # winfo_parent() should return the parent widget, but the
                # the current version of Tkinter returns a string.
                if type(parent) is str:
                    parent = self._hull._nametowidget(parent)
                master = parent.winfo_toplevel()
            self.transient(master)

        pushgrab(self._hull, globalMode, self.deactivate)
        command = self['activatecommand']
        if hasattr(command, '__call__'):
            command()
        self.wait_variable(self._wait)

        return self._result

    def deactivate(self, result=None):
        if not self._active:
            return
        self._active = 0

        # Restore the focus before withdrawing the window, since
        # otherwise the window manager may take the focus away so we
        # can't redirect it.  Also, return the grab to the next active
        # window in the stack, if any.
        popgrab(self._hull)

        command = self['deactivatecommand']
        if hasattr(command, '__call__'):
            command()

        self.withdraw()
        hidebusycursor(forceFocusRestore = 1)

        self._result = result
        self._wait.set(1)

    def active(self):
        return self._active

forwardmethods(MegaToplevel, tkinter.Toplevel, '_hull')

#=============================================================================

class MegaWidget(MegaArchetype):
    def __init__(self, parent = None, **kw):
        # Define the options for this megawidget.
        optiondefs = (
            ('hull_class',       self.__class__.__name__,  None),
        )
        self.defineoptions(kw, optiondefs)

        # Initialise the base class (after defining the options).
        MegaArchetype.__init__(self, parent, tkinter.Frame)

        # Check keywords and initialise options.
        self.initialiseoptions()

forwardmethods(MegaWidget, tkinter.Frame, '_hull')

#=============================================================================

# Public functions
#-----------------

_traceTk = 0
def tracetk(root = None, on = 1, withStackTrace = 0, file=None):
    global _withStackTrace
    global _traceTkFile
    global _traceTk

    if root is None:
        root = tkinter._default_root
    
    _withStackTrace = withStackTrace
    _traceTk = on
    if on == 1:
        # This causes trace not to work - not enabled by default in tk anymore?
        # if hasattr(root.tk, '__class__'):
        #   # Tracing already on
        #    return
        if file is None:
            _traceTkFile = sys.stderr
        else:
            _traceTkFile = file
        tk = _TraceTk(root.tk)
    else:
        if not hasattr(root.tk, '__class__'):
            # Tracing already off
            return
        tk = root.tk.getTclInterp()
    _setTkInterps(root, tk)

def showbusycursor():

    _addRootToToplevelBusyInfo()
    root = tkinter._default_root

    busyInfo = {
        'newBusyWindows' : [],
        'previousFocus' : None,
        'busyFocus' : None,
    }
    _busyStack.append(busyInfo)

    if _disableKeyboardWhileBusy:
        # Remember the focus as it is now, before it is changed.
        busyInfo['previousFocus'] = root.tk.call('focus')

    if not _havebltbusy(root):
        # No busy command, so don't call busy hold on any windows.
        return

    for (window, winInfo) in list(_toplevelBusyInfo.items()):
        if (window.state() != 'withdrawn' and not winInfo['isBusy']
                and not winInfo['excludeFromBusy']):
            busyInfo['newBusyWindows'].append(window)
            winInfo['isBusy'] = 1
            _busy_hold(window, winInfo['busyCursorName'])

            # Make sure that no events for the busy window get
            # through to Tkinter, otherwise it will crash in
            # _nametowidget with a 'KeyError: _Busy' if there is
            # a binding on the toplevel window.
            window.tk.call('bindtags', winInfo['busyWindow'], 'Pmw_Dummy_Tag')

            if _disableKeyboardWhileBusy:
                # Remember previous focus widget for this toplevel window
                # and set focus to the busy window, which will ignore all
                # keyboard events.
                winInfo['windowFocus'] = \
                        window.tk.call('focus', '-lastfor', window._w)
                window.tk.call('focus', winInfo['busyWindow'])
                busyInfo['busyFocus'] = winInfo['busyWindow']

    if len(busyInfo['newBusyWindows']) > 0:
        if os.name == 'nt':
            # NT needs an "update" before it will change the cursor.
            window.update()
        else:
            window.update_idletasks()

def hidebusycursor(forceFocusRestore = 0):

    # Remember the focus as it is now, before it is changed.
    root = tkinter._default_root
    if _disableKeyboardWhileBusy:
        currentFocus = root.tk.call('focus')

    # Pop the busy info off the stack.
    busyInfo = _busyStack[-1]
    del _busyStack[-1]

    for window in busyInfo['newBusyWindows']:
        # If this window has not been deleted, release the busy cursor.
        if window in _toplevelBusyInfo:
            winInfo = _toplevelBusyInfo[window]
            winInfo['isBusy'] = 0
            _busy_release(window)

            if _disableKeyboardWhileBusy:
                # Restore previous focus window for this toplevel window,
                # but only if is still set to the busy window (it may have
                # been changed).
                windowFocusNow = window.tk.call('focus', '-lastfor', window._w)
                if windowFocusNow == winInfo['busyWindow']:
                    try:
                        window.tk.call('focus', winInfo['windowFocus'])
                    except tkinter.TclError:
                        # Previous focus widget has been deleted. Set focus
                        # to toplevel window instead (can't leave focus on
                        # busy window).
                        window.focus_set()

    if _disableKeyboardWhileBusy:
        # Restore the focus, depending on whether the focus had changed
        # between the calls to showbusycursor and hidebusycursor.
        if forceFocusRestore or busyInfo['busyFocus'] == currentFocus:
            # The focus had not changed, so restore it to as it was before
            # the call to showbusycursor,
            previousFocus = busyInfo['previousFocus']
            if previousFocus is not None:
                try:
                    root.tk.call('focus', previousFocus)
                except tkinter.TclError:
                    # Previous focus widget has been deleted; forget it.
                    pass
        else:
            # The focus had changed, so restore it to what it had been
            # changed to before the call to hidebusycursor.
            root.tk.call('focus', currentFocus)

def clearbusycursor():
    while len(_busyStack) > 0:
        hidebusycursor()

def setbusycursorattributes(window, **kw):
    _addRootToToplevelBusyInfo()
    for name, value in list(kw.items()):
        if name == 'exclude':
            _toplevelBusyInfo[window]['excludeFromBusy'] = value
        elif name == 'cursorName':
            _toplevelBusyInfo[window]['busyCursorName'] = value
        else:
            raise KeyError('Unknown busycursor attribute "' + name + '"')

def _addRootToToplevelBusyInfo():
    # Include the Tk root window in the list of toplevels.  This must
    # not be called before Tkinter has had a chance to be initialised by
    # the application.

    root = tkinter._default_root
    if root == None:
        root = tkinter.Tk()
    if root not in _toplevelBusyInfo:
        _addToplevelBusyInfo(root)

def busycallback(command, updateFunction = None):
    if not hasattr(command, '__call__'):
        raise ValueError('cannot register non-command busy callback %s %s' % \
                (repr(command), type(command)))
    wrapper = _BusyWrapper(command, updateFunction)
    return wrapper.callback

_errorReportFile = None
_errorWindow = None

def reporterrorstofile(file = None):
    global _errorReportFile
    _errorReportFile = file

def displayerror(text):
    global _errorWindow

    if _errorReportFile is not None:
        _errorReportFile.write(text + '\n')
    else:
        # Print error on standard error as well as to error window.
        # Useful if error window fails to be displayed, for example
        # when exception is triggered in a <Destroy> binding for root
        # window.
        sys.stderr.write(text + '\n')

        if _errorWindow is None:
            # The error window has not yet been created.
            _errorWindow = _ErrorWindow()

        _errorWindow.showerror(text)

_root = None
_disableKeyboardWhileBusy = 1

def initialise(
        root = None,
        size = None,
        fontScheme = None,
        useTkOptionDb = 0,
        noBltBusy = 0,
        disableKeyboardWhileBusy = None,
):
    # Remember if show/hidebusycursor should ignore keyboard events.
    global _disableKeyboardWhileBusy
    if disableKeyboardWhileBusy is not None:
        _disableKeyboardWhileBusy = disableKeyboardWhileBusy

    # Do not use blt busy command if noBltBusy is set.  Otherwise,
    # use blt busy if it is available.
    global _haveBltBusy
    if noBltBusy:
        _haveBltBusy = 0

    # Save flag specifying whether the Tk option database should be
    # queried when setting megawidget option default values.
    global _useTkOptionDb
    _useTkOptionDb = useTkOptionDb

    # If we haven't been given a root window, use the default or
    # create one.
    if root is None:
        if tkinter._default_root is None:
            root = tkinter.Tk()
        else:
            root = tkinter._default_root

    # If this call is initialising a different Tk interpreter than the
    # last call, then re-initialise all global variables.  Assume the
    # last interpreter has been destroyed - ie:  Pmw does not (yet)
    # support multiple simultaneous interpreters.
    global _root
    if _root is not None and _root != root:
        global _busyStack
        global _errorWindow
        global _grabStack
        global _hullToMegaWidget
        global _toplevelBusyInfo
        _busyStack = []
        _errorWindow = None
        _grabStack = []
        _hullToMegaWidget = {}
        _toplevelBusyInfo = {}
    _root = root

    # Trap Tkinter Toplevel constructors so that a list of Toplevels
    # can be maintained.
    tkinter.Toplevel.title = __TkinterToplevelTitle

    # Trap Tkinter widget destruction so that megawidgets can be
    # destroyed when their hull widget is destoyed and the list of
    # Toplevels can be pruned.
    tkinter.Toplevel.destroy = __TkinterToplevelDestroy
    tkinter.Widget.destroy = __TkinterWidgetDestroy

    # Modify Tkinter's CallWrapper class to improve the display of
    # errors which occur in callbacks.
    tkinter.CallWrapper = __TkinterCallWrapper

    # Make sure we get to know when the window manager deletes the
    # root window.  Only do this if the protocol has not yet been set.
    # This is required if there is a modal dialog displayed and the
    # window manager deletes the root window.  Otherwise the
    # application will not exit, even though there are no windows.
    if root.protocol('WM_DELETE_WINDOW') == '':
        root.protocol('WM_DELETE_WINDOW', root.destroy)

    # Set the base font size for the application and set the
    # Tk option database font resources.
    _font_initialise(root, size, fontScheme)
    return root

def alignlabels(widgets, sticky = None):
    if len(widgets) == 0:
        return

    widgets[0].update_idletasks()

    # Determine the size of the maximum length label string.
    maxLabelWidth = 0
    for iwid in widgets:
        labelWidth = iwid.grid_bbox(0, 1)[2]
        if labelWidth > maxLabelWidth:
            maxLabelWidth = labelWidth

    # Adjust the margins for the labels such that the child sites and
    # labels line up.
    for iwid in widgets:
        if sticky is not None:
            iwid.component('label').grid(sticky=sticky)
        iwid.grid_columnconfigure(0, minsize = maxLabelWidth)
#=============================================================================

# Private routines
#-----------------
_callToTkReturned = 1
_recursionCounter = 1

class _TraceTk:
    def __init__(self, tclInterp):
        self.tclInterp = tclInterp

    def getTclInterp(self):
        return self.tclInterp

    # Calling from python into Tk.
    def call(self, *args, **kw):
        global _callToTkReturned
        global _recursionCounter

        _callToTkReturned = 0
        if len(args) == 1 and type(args[0]) == tuple:
            argStr = str(args[0])
        else:
            argStr = str(args)
        _traceTkFile.write('CALL  TK> %d:%s%s' %
                (_recursionCounter, '  ' * _recursionCounter, argStr))
        _recursionCounter = _recursionCounter + 1
        try:
            result = self.tclInterp.call(*args, **kw)
        except tkinter.TclError as errorString:
            _callToTkReturned = 1
            _recursionCounter = _recursionCounter - 1
            _traceTkFile.write('\nTK ERROR> %d:%s-> %s\n' %
                    (_recursionCounter, '  ' * _recursionCounter,
                            repr(errorString)))
            if _withStackTrace:
                _traceTkFile.write('CALL  TK> stack:\n')
                traceback.print_stack()
            raise tkinter.TclError(errorString)

        _recursionCounter = _recursionCounter - 1
        if _callToTkReturned:
            _traceTkFile.write('CALL RTN> %d:%s-> %s' %
                    (_recursionCounter, '  ' * _recursionCounter, repr(result)))
        else:
            _callToTkReturned = 1
            if result:
                _traceTkFile.write(' -> %s' % repr(result))
        _traceTkFile.write('\n')
        if _withStackTrace:
            _traceTkFile.write('CALL  TK> stack:\n')
            traceback.print_stack()

        _traceTkFile.flush()
        return result

    def __getattr__(self, key):
        return getattr(self.tclInterp, key)

def _setTkInterps(window, tk):
    window.tk = tk
    for child in list(window.children.values()):
        _setTkInterps(child, tk)

#=============================================================================

# Functions to display a busy cursor.  Keep a list of all toplevels
# and display the busy cursor over them.  The list will contain the Tk
# root toplevel window as well as all other toplevel windows.
# Also keep a list of the widget which last had focus for each
# toplevel.

# Map from toplevel windows to
#     {'isBusy', 'windowFocus', 'busyWindow',
#         'excludeFromBusy', 'busyCursorName'}
_toplevelBusyInfo = {}

# Pmw needs to know all toplevel windows, so that it can call blt busy
# on them.  This is a hack so we get notified when a Tk topevel is
# created.  Ideally, the __init__ 'method' should be overridden, but
# it is a 'read-only special attribute'.  Luckily, title() is always
# called from the Tkinter Toplevel constructor.

def _addToplevelBusyInfo(window):
    if window._w == '.':
        busyWindow = '._Busy'
    else:
        busyWindow = window._w + '._Busy'

    _toplevelBusyInfo[window] = {
        'isBusy' : 0,
        'windowFocus' : None,
        'busyWindow' : busyWindow,
        'excludeFromBusy' : 0,
        'busyCursorName' : None,
    }

def __TkinterToplevelTitle(self, *args):
    # If this is being called from the constructor, include this
    # Toplevel in the list of toplevels and set the initial
    # WM_DELETE_WINDOW protocol to destroy() so that we get to know
    # about it.
    if self not in _toplevelBusyInfo:
        _addToplevelBusyInfo(self)
        self._Pmw_WM_DELETE_name = self.register(self.destroy, None, 0)
        self.protocol('WM_DELETE_WINDOW', self._Pmw_WM_DELETE_name)

    return tkinter.Wm.title(*(self,) + args)

_haveBltBusy = None
def _havebltbusy(window):
    global _busy_hold, _busy_release, _haveBltBusy
    if _haveBltBusy is None:
        from . import PmwBlt
        _haveBltBusy = PmwBlt.havebltbusy(window)
        _busy_hold = PmwBlt.busy_hold
        if os.name == 'nt':
            # There is a bug in Blt 2.4i on NT where the busy window
            # does not follow changes in the children of a window.
            # Using forget works around the problem.
            _busy_release = PmwBlt.busy_forget
        else:
            _busy_release = PmwBlt.busy_release
    return _haveBltBusy

class _BusyWrapper:
    def __init__(self, command, updateFunction):
        self._command = command
        self._updateFunction = updateFunction

    def callback(self, *args):
        showbusycursor()
        rtn = self._command(*args)

        # Call update before hiding the busy windows to clear any
        # events that may have occurred over the busy windows.
        if hasattr(self._updateFunction, '__call__'):
            self._updateFunction()

        hidebusycursor()
        return rtn

#=============================================================================

def drawarrow(canvas, color, direction, tag, baseOffset = 0.25, edgeOffset = 0.15):
    canvas.delete(tag)

    bw = (int(canvas['borderwidth']) +
            int(canvas['highlightthickness']))
    width = int(canvas['width'])
    height = int(canvas['height'])

    if direction in ('up', 'down'):
        majorDimension = height
        minorDimension = width
    else:
        majorDimension = width
        minorDimension = height

    offset = round(baseOffset * majorDimension)
    if direction in ('down', 'right'):
        base = bw + offset
        apex = bw + majorDimension - offset
    else:
        base = bw + majorDimension - offset
        apex = bw + offset

    if minorDimension > 3 and minorDimension % 2 == 0:
        minorDimension = minorDimension - 1
    half = int(minorDimension * (1 - 2 * edgeOffset)) / 2
    low = round(bw + edgeOffset * minorDimension)
    middle = low + half
    high = low + 2 * half

    if direction in ('up', 'down'):
        coords = (low, base, high, base, middle, apex)
    else:
        coords = (base, low, base, high, apex, middle)
    kw = {'fill' : color, 'outline' : color, 'tag' : tag}
    canvas.create_polygon(*coords, **kw)

#=============================================================================

# Modify the Tkinter destroy methods so that it notifies us when a Tk
# toplevel or frame is destroyed.

# A map from the 'hull' component of a megawidget to the megawidget.
# This is used to clean up a megawidget when its hull is destroyed.
_hullToMegaWidget = {}

def __TkinterToplevelDestroy(tkWidget):
    if tkWidget in _hullToMegaWidget:
        mega = _hullToMegaWidget[tkWidget]
        try:
            mega.destroy()
        except:
            _reporterror(mega.destroy, ())
    else:
        # Delete the busy info structure for this toplevel (if the
        # window was created before Pmw.initialise() was called, it
        # will not have any.
        if tkWidget in _toplevelBusyInfo:
            del _toplevelBusyInfo[tkWidget]
        if hasattr(tkWidget, '_Pmw_WM_DELETE_name'):
            tkWidget.tk.deletecommand(tkWidget._Pmw_WM_DELETE_name)
            del tkWidget._Pmw_WM_DELETE_name
        tkinter.BaseWidget.destroy(tkWidget)

def __TkinterWidgetDestroy(tkWidget):
    if tkWidget in _hullToMegaWidget:
        mega = _hullToMegaWidget[tkWidget]
        try:
            mega.destroy()
        except:
            _reporterror(mega.destroy, ())
    else:
        tkinter.BaseWidget.destroy(tkWidget)

#=============================================================================

# Add code to Tkinter to improve the display of errors which occur in
# callbacks.

class __TkinterCallWrapper:
    def __init__(self, func, subst, widget):
        self.func = func
        self.subst = subst
        self.widget = widget

    # Calling back from Tk into python.
    def __call__(self, *args):
        try:
            if self.subst:
                args = self.subst(*args)
            if _traceTk:
                if not _callToTkReturned:
                    _traceTkFile.write('\n')
                if hasattr(self.func, 'im_class'):
                    name = self.func.__self__.__class__.__name__ + '.' + \
                        self.func.__name__
                else:
                    name = self.func.__name__
                if len(args) == 1 and hasattr(args[0], 'type'):
                    # The argument to the callback is an event.
                    eventName = _eventTypeToName[int(args[0].type)]
                    if eventName in ('KeyPress', 'KeyRelease',):
                        argStr = '(%s %s Event: %s)' % \
                            (eventName, args[0].keysym, args[0].widget)
                    else:
                        argStr = '(%s Event, %s)' % (eventName, args[0].widget)
                else:
                    argStr = str(args)
                _traceTkFile.write('CALLBACK> %d:%s%s%s\n' %
                    (_recursionCounter, '  ' * _recursionCounter, name, argStr))
                _traceTkFile.flush()
            return self.func(*args)
        except SystemExit as msg:
            raise SystemExit(msg)
        except:
            _reporterror(self.func, args)

_eventTypeToName = {
    2 : 'KeyPress',         15 : 'VisibilityNotify',   28 : 'PropertyNotify',
    3 : 'KeyRelease',       16 : 'CreateNotify',       29 : 'SelectionClear',
    4 : 'ButtonPress',      17 : 'DestroyNotify',      30 : 'SelectionRequest',
    5 : 'ButtonRelease',    18 : 'UnmapNotify',        31 : 'SelectionNotify',
    6 : 'MotionNotify',     19 : 'MapNotify',          32 : 'ColormapNotify',
    7 : 'EnterNotify',      20 : 'MapRequest',         33 : 'ClientMessage',
    8 : 'LeaveNotify',      21 : 'ReparentNotify',     34 : 'MappingNotify',
    9 : 'FocusIn',          22 : 'ConfigureNotify',    35 : 'VirtualEvents',
    10 : 'FocusOut',        23 : 'ConfigureRequest',   36 : 'ActivateNotify',
    11 : 'KeymapNotify',    24 : 'GravityNotify',      37 : 'DeactivateNotify',
    12 : 'Expose',          25 : 'ResizeRequest',      38 : 'MouseWheelEvent',
    13 : 'GraphicsExpose',  26 : 'CirculateNotify',
    14 : 'NoExpose',        27 : 'CirculateRequest',
}

def _reporterror(func, args):
    # Fetch current exception values.
    exc_type, exc_value, exc_traceback = sys.exc_info()

    # Give basic information about the callback exception.
    if type(exc_type) == type:
        # Handle python 1.5 class exceptions.
        exc_type = exc_type.__name__
    msg = str(exc_type) + ' Exception in Tk callback\n'
    msg = msg + '  Function: %s (type: %s)\n' % (repr(func), type(func))
    msg = msg + '  Args: %s\n' % str(args)

    if type(args) == tuple and len(args) > 0 and \
            hasattr(args[0], 'type'):
        eventArg = 1
    else:
        eventArg = 0

    # If the argument to the callback is an event, add the event type.
    if eventArg:
        eventNum = int(args[0].type)
        if eventNum in list(_eventTypeToName.keys()):
            msg = msg + '  Event type: %s (type num: %d)\n' % \
                    (_eventTypeToName[eventNum], eventNum)
        else:
            msg = msg + '  Unknown event type (type num: %d)\n' % eventNum

    # Add the traceback.
    msg = msg + 'Traceback (innermost last):\n'
    for tr in traceback.extract_tb(exc_traceback):
        msg = msg + '  File "%s", line %s, in %s\n' % (tr[0], tr[1], tr[2])
        msg = msg + '    %s\n' % tr[3]
    msg = msg + '%s: %s\n' % (exc_type, exc_value)

    # If the argument to the callback is an event, add the event contents.
    if eventArg:
        msg = msg + '\n================================================\n'
        msg = msg + '  Event contents:\n'
        keys = list(args[0].__dict__.keys())
        keys.sort()
        for key in keys:
            msg = msg + '    %s: %s\n' % (key, args[0].__dict__[key])

    clearbusycursor()
    try:
        displayerror(msg)
    except:
        pass

class _ErrorWindow:
    def __init__(self):

        self._errorQueue = []
        self._errorCount = 0
        self._open = 0
        self._firstShowing = 1

        # Create the toplevel window
        self._top = tkinter.Toplevel()
        self._top.protocol('WM_DELETE_WINDOW', self._hide)
        self._top.title('Error in background function')
        self._top.iconname('Background error')

        # Create the text widget and scrollbar in a frame
        upperframe = tkinter.Frame(self._top)

        scrollbar = tkinter.Scrollbar(upperframe, orient='vertical')
        scrollbar.pack(side = 'right', fill = 'y')

        self._text = tkinter.Text(upperframe, yscrollcommand=scrollbar.set)
        self._text.pack(fill = 'both', expand = 1)
        scrollbar.configure(command=self._text.yview)

        # Create the buttons and label in a frame
        lowerframe = tkinter.Frame(self._top)

        ignore = tkinter.Button(lowerframe,
                text = 'Ignore remaining errors', command = self._hide)
        ignore.pack(side='left')

        self._nextError = tkinter.Button(lowerframe,
                text = 'Show next error', command = self._next)
        self._nextError.pack(side='left')

        self._label = tkinter.Label(lowerframe, relief='ridge')
        self._label.pack(side='left', fill='x', expand=1)

        # Pack the lower frame first so that it does not disappear
        # when the window is resized.
        lowerframe.pack(side = 'bottom', fill = 'x')
        upperframe.pack(side = 'bottom', fill = 'both', expand = 1)

    def showerror(self, text):
        if self._open:
            self._errorQueue.append(text)
        else:
            self._display(text)
            self._open = 1

        # Display the error window in the same place it was before.
        if self._top.state() == 'normal':
            # If update_idletasks is not called here, the window may
            # be placed partially off the screen.  Also, if it is not
            # called and many errors are generated quickly in
            # succession, the error window may not display errors
            # until the last one is generated and the interpreter
            # becomes idle.
            # XXX: remove this, since it causes omppython to go into an
            # infinite loop if an error occurs in an omp callback.
            # self._top.update_idletasks()

            pass
        else:
            if self._firstShowing:
                geom = None
            else:
                geometry = self._top.geometry()
                index = str.find(geometry, '+')
                if index >= 0:
                    geom = geometry[index:]
                else:
                    geom = None
            setgeometryanddeiconify(self._top, geom)

        if self._firstShowing:
            self._firstShowing = 0
        else:
            self._top.tkraise()

        self._top.focus()

        self._updateButtons()

        # Release any grab, so that buttons in the error window work.
        releasegrabs()

    def _hide(self):
        self._errorCount = self._errorCount + len(self._errorQueue)
        self._errorQueue = []
        self._top.withdraw()
        self._open = 0

    def _next(self):
        # Display the next error in the queue.

        text = self._errorQueue[0]
        del self._errorQueue[0]

        self._display(text)
        self._updateButtons()

    def _display(self, text):
        self._errorCount = self._errorCount + 1
        text = 'Error: %d\n%s' % (self._errorCount, text)
        self._text.delete('1.0', 'end')
        self._text.insert('end', text)

    def _updateButtons(self):
        numQueued = len(self._errorQueue)
        if numQueued > 0:
            self._label.configure(text='%d more errors' % numQueued)
            self._nextError.configure(state='normal')
        else:
            self._label.configure(text='No more errors')
            self._nextError.configure(state='disabled')

_bltImported = 1
_bltbusyOK = 0

######################################################################
### File: PmwDialog.py
# Based on iwidgets2.2.0/dialog.itk and iwidgets2.2.0/dialogshell.itk code.

# Convention:
#   Each dialog window should have one of these as the rightmost button:
#     Close         Close a window which only displays information.
#     Cancel        Close a window which may be used to change the state of
#                   the application.

import sys
import types
import tkinter
import Pmw
import collections

# A Toplevel with a ButtonBox and child site.

class Dialog(Pmw.MegaToplevel):
    def __init__(self, parent = None, **kw):

        # Define the megawidget options.
        
        optiondefs = (
            ('buttonbox_hull_borderwidth',   1,         None),
            ('buttonbox_hull_relief',        'raised',  None),
            ('buttonboxpos',                 's',       INITOPT),
            ('buttons',                      ('OK',),   self._buttons),
            ('command',                      None,      None),
            ('dialogchildsite_borderwidth',  1,         None),
            ('dialogchildsite_relief',       'raised',  None),
            ('defaultbutton',                None,      self._defaultButton),
            ('master',                       'parent',  None),
            ('separatorwidth',               0,         INITOPT),
        )
        self.defineoptions(kw, optiondefs)

        # Initialise the base class (after defining the options).
        Pmw.MegaToplevel.__init__(self, parent)

        # Create the components.

        oldInterior = Pmw.MegaToplevel.interior(self)

        # Set up pack options according to the position of the button box.
        pos = self['buttonboxpos']
        if pos not in 'nsew':
            raise ValueError('bad buttonboxpos option "%s":  should be n, s, e, or w' \
                    % pos)

        if pos in 'ns':
            orient = 'horizontal'
            fill = 'x'
            if pos == 'n':
                side = 'top'
            else:
                side = 'bottom'
        else:
            orient = 'vertical'
            fill = 'y'
            if pos == 'w':
                side = 'left'
            else:
                side = 'right'

        # Create the button box.
        self._buttonBox = self.createcomponent('buttonbox',
                (), None,
                Pmw.ButtonBox, (oldInterior,), orient = orient)
        self._buttonBox.pack(side = side, fill = fill)

        # Create the separating line.
        width = self['separatorwidth']
        if width > 0:
            self._separator = self.createcomponent('separator',
                    (), None,
                    tkinter.Frame, (oldInterior,), relief = 'sunken',
                    height = width, width = width, borderwidth = width / 2)
            self._separator.pack(side = side, fill = fill)

        # Create the child site.
        self.__dialogChildSite = self.createcomponent('dialogchildsite',
                (), None,
                tkinter.Frame, (oldInterior,))
        self.__dialogChildSite.pack(side=side, fill='both', expand=1)

        self.oldButtons = ()
        self.oldDefault = None

        self.bind('<Return>', self._invokeDefault)
        self.userdeletefunc(self._doCommand)
        self.usermodaldeletefunc(self._doCommand)

        # Check keywords and initialise options.
        self.initialiseoptions()

    def interior(self):
        return self.__dialogChildSite

    def invoke(self, index = Pmw.DEFAULT):
        return self._buttonBox.invoke(index)

    def _invokeDefault(self, event):
        try:
            self._buttonBox.index(Pmw.DEFAULT)
        except ValueError:
            return
        self._buttonBox.invoke()

    def _doCommand(self, name = None):
        if name is not None and self.active() and \
                Pmw.grabstacktopwindow() != self.component('hull'):
            # This is a modal dialog but is not on the top of the grab
            # stack (ie:  should not have the grab), so ignore this
            # event.  This seems to be a bug in Tk and may occur in
            # nested modal dialogs.
            #
            # An example is the PromptDialog demonstration.  To
            # trigger the problem, start the demo, then move the mouse
            # to the main window, hit <TAB> and then <TAB> again.  The
            # highlight border of the "Show prompt dialog" button
            # should now be displayed.  Now hit <SPACE>, <RETURN>,
            # <RETURN> rapidly several times.  Eventually, hitting the
            # return key invokes the password dialog "OK" button even
            # though the confirm dialog is active (and therefore
            # should have the keyboard focus).  Observed under Solaris
            # 2.5.1, python 1.5.2 and Tk8.0.

            # TODO:  Give focus to the window on top of the grabstack.
            return

        command = self['command']
        if hasattr(command, '__call__'):
            return command(name)
        else:
            if self.active():
                self.deactivate(name)
            else:
                self.withdraw()

    def _buttons(self):
        buttons = self['buttons']
        if type(buttons) != tuple and type(buttons) != list:
            raise ValueError('bad buttons option "%s": should be a tuple' % str(buttons))
        if self.oldButtons == buttons:
            return

        self.oldButtons = buttons

        for index in range(self._buttonBox.numbuttons()):
            self._buttonBox.delete(0)
        for name in buttons:
            self._buttonBox.add(name,
                command=lambda self=self, name=name: self._doCommand(name))

        if len(buttons) > 0:
            defaultbutton = self['defaultbutton']
            if defaultbutton is None:
                self._buttonBox.setdefault(None)
            else:
                try:
                    self._buttonBox.index(defaultbutton)
                except ValueError:
                    pass
                else:
                    self._buttonBox.setdefault(defaultbutton)
        self._buttonBox.alignbuttons()

    def _defaultButton(self):
        defaultbutton = self['defaultbutton']
        if self.oldDefault == defaultbutton:
            return

        self.oldDefault = defaultbutton

        if len(self['buttons']) > 0:
            if defaultbutton is None:
                self._buttonBox.setdefault(None)
            else:
                try:
                    self._buttonBox.index(defaultbutton)
                except ValueError:
                    pass
                else:
                    self._buttonBox.setdefault(defaultbutton)

######################################################################
### File: PmwTimeFuncs.py
# Functions for dealing with dates and times.

import re
import string

def timestringtoseconds(text, separator = ':'):
    inputList = text.strip().split(separator)

    if len(inputList) != 3:
        raise ValueError('invalid value: ' + text)

    sign = 1
    if len(inputList[0]) > 0 and inputList[0][0] in ('+', '-'):
        if inputList[0][0] == '-':
            sign = -1
        inputList[0] = inputList[0][1:]

    if re.search('[^0-9]', ''.join(inputList)) is not None:
        raise ValueError('invalid value: ' + text)

    hour = int(inputList[0])
    minute = int(inputList[1])
    second = int(inputList[2])
    
    if minute >= 60 or second >= 60:
        raise ValueError('invalid value: ' + text)
    return sign * (hour * 60 * 60 + minute * 60 + second)

_year_pivot = 50
_century = 2000

def setyearpivot(pivot, century = None):
    global _year_pivot
    global _century
    oldvalues = (_year_pivot, _century)
    _year_pivot = pivot
    if century is not None:
        _century = century
    return oldvalues

def datestringtojdn(text, fmt = 'ymd', separator = '/'):
    inputList = text.strip().split(separator)
    if len(inputList) != 3:
        raise ValueError('invalid value: ' + text)

    if re.search('[^0-9]', ''.join(inputList)) is not None:
        raise ValueError('invalid value: ' + text)
    formatList = list(fmt)
    day = int(inputList[formatList.index('d')])
    month = int(inputList[formatList.index('m')])
    year = int(inputList[formatList.index('y')])

    if _year_pivot is not None:
        if year >= 0 and year < 100:
            if year <= _year_pivot:
                year = year + _century
            else:
                year = year + _century - 100

    jdn = ymdtojdn(year, month, day)

    if jdntoymd(jdn) != (year, month, day):
        raise ValueError('invalid value: ' + text)
    return jdn

def _cdiv(a, b):
    # Return a / b as calculated by most C language implementations,
    # assuming both a and b are integers.

    if a * b > 0:
        return int(a / b)
    else:
        return -int(abs(a) / abs(b))

def ymdtojdn(year, month, day, julian = -1, papal = 1):

    # set Julian flag if auto set
    if julian < 0:
        if papal:                          # Pope Gregory XIII's decree
            lastJulianDate = 15821004     # last day to use Julian calendar
        else:                              # British-American usage
            lastJulianDate = 17520902     # last day to use Julian calendar

        julian = ((year * 100) + month) * 100 + day  <=  lastJulianDate

    if year < 0:
        # Adjust BC year
        year = year + 1

    if julian:
        return 367 * year - _cdiv(7 * (year + 5001 + _cdiv((month - 9), 7)), 4) + \
            _cdiv(275 * month, 9) + day + 1729777
    else:
        return (day - 32076) + \
            _cdiv(1461 * (year + 4800 + _cdiv((month - 14), 12)), 4) + \
            _cdiv(367 * (month - 2 - _cdiv((month - 14), 12) * 12), 12) - \
            _cdiv((3 * _cdiv((year + 4900 + _cdiv((month - 14), 12)), 100)), 4) + \
            1            # correction by rdg

def jdntoymd(jdn, julian = -1, papal = 1):

    # set Julian flag if auto set
    if julian < 0:
        if papal:                          # Pope Gregory XIII's decree
            lastJulianJdn = 2299160       # last jdn to use Julian calendar
        else:                              # British-American usage
            lastJulianJdn = 2361221       # last jdn to use Julian calendar

        julian = (jdn <= lastJulianJdn);

    x = jdn + 68569
    if julian:
        x = x + 38
        daysPer400Years = 146100
        fudgedDaysPer4000Years = 1461000 + 1
    else:
        daysPer400Years = 146097
        fudgedDaysPer4000Years = 1460970 + 31

    z = _cdiv(4 * x, daysPer400Years)
    x = x - _cdiv((daysPer400Years * z + 3), 4)
    y = _cdiv(4000 * (x + 1), fudgedDaysPer4000Years)
    x = x - _cdiv(1461 * y, 4) + 31
    m = _cdiv(80 * x, 2447)
    d = x - _cdiv(2447 * m, 80)
    x = _cdiv(m, 11)
    m = m + 2 - 12 * x
    y = 100 * (z - 49) + y + x

    # Convert from longs to integers.
    yy = int(y)
    mm = int(m)
    dd = int(d)

    if yy <= 0:
        # Adjust BC years.
        yy = yy - 1

    return (yy, mm, dd)

def stringtoreal(text, separator = '.'):
    if separator != '.':
        if text.find('.') >= 0:
            raise ValueError('invalid value: ' + text)
        index = text.find(separator)
        if index >= 0:
            text = text[:index] + '.' + text[index + 1:]
    return float(text)

######################################################################
### File: PmwBalloon.py
import os
import string
import tkinter
import Pmw
import collections

class Balloon(Pmw.MegaToplevel):
    def __init__(self, parent = None, **kw):

        # Define the megawidget options.
        optiondefs = (
            ('initwait',                 500,            None), # milliseconds
            ('label_background',         'lightyellow',  None),
            ('label_foreground',         'black',        None),
            ('label_justify',            'left',         None),
            ('master',                   'parent',       None),
            ('relmouse',                 'none',         self._relmouse),
            ('state',                    'both',         self._state),
            ('statuscommand',            None,           None),
            ('xoffset',                  20,             None), # pixels
            ('yoffset',                  1,              None), # pixels
            ('hull_highlightthickness',  1,              None),
            ('hull_highlightbackground', 'black',        None),
        )
        self.defineoptions(kw, optiondefs)

        # Initialise the base class (after defining the options).
        Pmw.MegaToplevel.__init__(self, parent)

        self.withdraw()
        self.overrideredirect(1)

        # Create the components.
        interior = self.interior()
        self._label = self.createcomponent('label',
                (), None,
                tkinter.Label, (interior,))
        self._label.pack()

        # The default hull configuration options give a black border
        # around the balloon, but avoids a black 'flash' when the
        # balloon is deiconified, before the text appears.
        if 'hull_background' not in kw:
            self.configure(hull_background = \
                    str(self._label.cget('background')))

        # Initialise instance variables.
        self._timer = None

        # The widget or item that is currently triggering the balloon.
        # It is None if the balloon is not being displayed.  It is a
        # one-tuple if the balloon is being displayed in response to a
        # widget binding (value is the widget).  It is a two-tuple if
        # the balloon is being displayed in response to a canvas or
        # text item binding (value is the widget and the item).
        self._currentTrigger = None

        # Check keywords and initialise options.
        self.initialiseoptions()

    def destroy(self):
        if self._timer is not None:
            self.after_cancel(self._timer)
            self._timer = None
        Pmw.MegaToplevel.destroy(self)

    def bind(self, widget, balloonHelp, statusHelp = None):

        # If a previous bind for this widget exists, remove it.
        self.unbind(widget)

        if balloonHelp is None and statusHelp is None:
            return

        if statusHelp is None:
            statusHelp = balloonHelp
        enterId = widget.bind('<Enter>',
                lambda event, self = self, w = widget,
                        sHelp = statusHelp, bHelp = balloonHelp:
                                self._enter(event, w, sHelp, bHelp, 0))

        # Set Motion binding so that if the pointer remains at rest
        # within the widget until the status line removes the help and
        # then the pointer moves again, then redisplay the help in the
        # status line.
        # Note:  The Motion binding only works for basic widgets, and
        # the hull of megawidgets but not for other megawidget components.
        motionId = widget.bind('<Motion>',
                lambda event = None, self = self, statusHelp = statusHelp:
                        self.showstatus(statusHelp))

        leaveId = widget.bind('<Leave>', self._leave)
        buttonId = widget.bind('<ButtonPress>', self._buttonpress)

        # Set Destroy binding so that the balloon can be withdrawn and
        # the timer can be cancelled if the widget is destroyed.
        destroyId = widget.bind('<Destroy>', self._destroy)

        # Use the None item in the widget's private Pmw dictionary to
        # store the widget's bind callbacks, for later clean up.
        if not hasattr(widget, '_Pmw_BalloonBindIds'):
            widget._Pmw_BalloonBindIds = {}
        widget._Pmw_BalloonBindIds[None] = \
                (enterId, motionId, leaveId, buttonId, destroyId)

    def unbind(self, widget):
        if hasattr(widget, '_Pmw_BalloonBindIds'):
            if None in widget._Pmw_BalloonBindIds:
                (enterId, motionId, leaveId, buttonId, destroyId) = \
                        widget._Pmw_BalloonBindIds[None]
                # Need to pass in old bindings, so that Tkinter can
                # delete the commands.  Otherwise, memory is leaked.
                widget.unbind('<Enter>', enterId)
                widget.unbind('<Motion>', motionId)
                widget.unbind('<Leave>', leaveId)
                widget.unbind('<ButtonPress>', buttonId)
                widget.unbind('<Destroy>', destroyId)
                del widget._Pmw_BalloonBindIds[None]

        if self._currentTrigger is not None and len(self._currentTrigger) == 1:
            # The balloon is currently being displayed and the current
            # trigger is a widget.
            triggerWidget = self._currentTrigger[0]
            if triggerWidget == widget:
                if self._timer is not None:
                    self.after_cancel(self._timer)
                    self._timer = None
                self.withdraw()
                self.clearstatus()
                self._currentTrigger = None

    def tagbind(self, widget, tagOrItem, balloonHelp, statusHelp = None):

        # If a previous bind for this widget's tagOrItem exists, remove it.
        self.tagunbind(widget, tagOrItem)

        if balloonHelp is None and statusHelp is None:
            return

        if statusHelp is None:
            statusHelp = balloonHelp
        enterId = widget.tag_bind(tagOrItem, '<Enter>',
                lambda event, self = self, w = widget,
                        sHelp = statusHelp, bHelp = balloonHelp, tag = tagOrItem:
                                self._enter(event, w, sHelp, bHelp, 1, tag))
        motionId = widget.tag_bind(tagOrItem, '<Motion>',
                lambda event = None, self = self, statusHelp = statusHelp:
                        self.showstatus(statusHelp))
        leaveId = widget.tag_bind(tagOrItem, '<Leave>', self._leave)
        buttonId = widget.tag_bind(tagOrItem, '<ButtonPress>', self._buttonpress)

        # Use the tagOrItem item in the widget's private Pmw dictionary to
        # store the tagOrItem's bind callbacks, for later clean up.
        if not hasattr(widget, '_Pmw_BalloonBindIds'):
            widget._Pmw_BalloonBindIds = {}
        widget._Pmw_BalloonBindIds[tagOrItem] = \
                (enterId, motionId, leaveId, buttonId)

    def tagunbind(self, widget, tagOrItem):
        if hasattr(widget, '_Pmw_BalloonBindIds'):
            if tagOrItem in widget._Pmw_BalloonBindIds:
                (enterId, motionId, leaveId, buttonId) = \
                        widget._Pmw_BalloonBindIds[tagOrItem]
                widget.tag_unbind(tagOrItem, '<Enter>', enterId)
                widget.tag_unbind(tagOrItem, '<Motion>', motionId)
                widget.tag_unbind(tagOrItem, '<Leave>', leaveId)
                widget.tag_unbind(tagOrItem, '<ButtonPress>', buttonId)
                del widget._Pmw_BalloonBindIds[tagOrItem]

        if self._currentTrigger is None:
            # The balloon is not currently being displayed.
            return

        if len(self._currentTrigger) == 1:
            # The current trigger is a widget.
            return

        if len(self._currentTrigger) == 2:
            # The current trigger is a canvas item.
            (triggerWidget, triggerItem) = self._currentTrigger
            if triggerWidget == widget and triggerItem == tagOrItem:
                if self._timer is not None:
                    self.after_cancel(self._timer)
                    self._timer = None
                self.withdraw()
                self.clearstatus()
                self._currentTrigger = None
        else: # The current trigger is a text item.
            (triggerWidget, x, y) = self._currentTrigger
            if triggerWidget == widget:
                currentPos = widget.index('@%d,%d' % (x, y))
                currentTags = widget.tag_names(currentPos)
                if tagOrItem in currentTags:
                    if self._timer is not None:
                        self.after_cancel(self._timer)
                        self._timer = None
                    self.withdraw()
                    self.clearstatus()
                    self._currentTrigger = None

    def showstatus(self, statusHelp):
        if self['state'] in ('status', 'both'):
            cmd = self['statuscommand']
            if hasattr(cmd, '__call__'):
                cmd(statusHelp)

    def clearstatus(self):
        self.showstatus(None)

    def _state(self):
        if self['state'] not in ('both', 'balloon', 'status', 'none'):
            raise ValueError('bad state option ' + repr(self['state']) + \
                ': should be one of \'both\', \'balloon\', ' + \
                '\'status\' or \'none\'')

    def _relmouse(self):
        if self['relmouse'] not in ('both', 'x', 'y', 'none'):
            raise ValueError('bad relmouse option ' + repr(self['relmouse'])+ \
                ': should be one of \'both\', \'x\', ' + '\'y\' or \'none\'')

    def _enter(self, event, widget, statusHelp, balloonHelp, isItem, tagOrItem = None):

        # Do not display balloon if mouse button is pressed.  This
        # will only occur if the button was pressed inside a widget,
        # then the mouse moved out of and then back into the widget,
        # with the button still held down.  The number 0x1f00 is the
        # button mask for the 5 possible buttons in X.
        buttonPressed = (event.state & 0x1f00) != 0

        if not buttonPressed and balloonHelp is not None and \
                self['state'] in ('balloon', 'both'):
            if self._timer is not None:
                self.after_cancel(self._timer)
                self._timer = None

            self._timer = self.after(self['initwait'],
                    lambda self = self, widget = widget, help = balloonHelp,
                            isItem = isItem:
                            self._showBalloon(widget, help, isItem, tagOrItem))

        if isItem:
            if hasattr(widget, 'canvasx'):
                # The widget is a canvas.
                item = widget.find_withtag('current')
                if len(item) > 0:
                    item = item[0]
                else:
                    item = None
                self._currentTrigger = (widget, item)
            else:
                # The widget is a text widget.
                self._currentTrigger = (widget, event.x, event.y)
        else:
            self._currentTrigger = (widget,)

        self.showstatus(statusHelp)

    def _leave(self, event):
        if self._timer is not None:
            self.after_cancel(self._timer)
            self._timer = None
        self.withdraw()
        self.clearstatus()
        self._currentTrigger = None

    def _destroy(self, event):

        # Only withdraw the balloon and cancel the timer if the widget
        # being destroyed is the widget that triggered the balloon.
        # Note that in a Tkinter Destroy event, the widget field is a
        # string and not a widget as usual.

        if self._currentTrigger is None:
            # The balloon is not currently being displayed
            return

        if len(self._currentTrigger) == 1:
            # The current trigger is a widget (not an item)
            triggerWidget = self._currentTrigger[0]
            if str(triggerWidget) == event.widget:
                if self._timer is not None:
                    self.after_cancel(self._timer)
                    self._timer = None
                self.withdraw()
                self.clearstatus()
                self._currentTrigger = None

    def _buttonpress(self, event):
        if self._timer is not None:
            self.after_cancel(self._timer)
            self._timer = None
        self.withdraw()
        self._currentTrigger = None

    def _showBalloon(self, widget, balloonHelp, isItem, tagOrItem = None):

        self._label.configure(text = balloonHelp)

        # First, display the balloon offscreen to get dimensions.
        screenWidth = self.winfo_screenwidth()
        screenHeight = self.winfo_screenheight()
        self.geometry('+%d+0' % (screenWidth + 1))
        self.update_idletasks()

        if isItem:
            # Get the bounding box of the current item.
            bbox = widget.bbox('current')
            if bbox is None:
                # The item that triggered the balloon has disappeared,
                # perhaps by a user's timer event that occured between
                # the <Enter> event and the 'initwait' timer calling
                # this method.
                return

            # The widget is either a text or canvas.  The meaning of
            # the values returned by the bbox method is different for
            # each, so use the existence of the 'canvasx' method to
            # distinguish between them.
            if hasattr(widget, 'canvasx'):
                # The widget is a canvas.  Place balloon under canvas
                # item.  The positions returned by bbox are relative
                # to the entire canvas, not just the visible part, so
                # need to convert to window coordinates.
                leftrel = bbox[0] - widget.canvasx(0)
                toprel = bbox[1] - widget.canvasy(0)
                bottomrel = bbox[3] - widget.canvasy(0)
            else:
                # The widget is a text widget.  Place balloon under
                # the character closest to the mouse.  The positions
                # returned by bbox are relative to the text widget
                # window (ie the visible part of the text only).
                if tagOrItem is not None:
                    index = widget.index('current')
                    while widget.compare(index, '>', '1.0'):
                        prev_index = widget.index('%s-1c' % index)
                        if tagOrItem in widget.tag_names(prev_index):
                            index = prev_index
                            newbbox = widget.bbox(index)
                            if newbbox == None:
                                break
                            bbox = newbbox
                        else:
                            break
                leftrel = bbox[0]
                toprel = bbox[1]
                bottomrel = bbox[1] + bbox[3]
        else:
            leftrel = 0
            toprel = 0
            bottomrel = widget.winfo_height()

        xpointer, ypointer = widget.winfo_pointerxy()   # -1 if off screen

        if xpointer >= 0 and self['relmouse'] in ('both', 'x'):
            x = xpointer
        else:
            x = leftrel + widget.winfo_rootx()
        x = x + self['xoffset']

        if ypointer >= 0 and self['relmouse'] in ('both', 'y'):
            y = ypointer
        else:
            y = bottomrel + widget.winfo_rooty()
        y = y + self['yoffset']
        edges = (int(str(self.cget('hull_highlightthickness'))) +
            int(str(self.cget('hull_borderwidth')))) * 2
        if x + self._label.winfo_reqwidth() + edges > screenWidth:
            x = screenWidth - self._label.winfo_reqwidth() - edges

        if y + self._label.winfo_reqheight() + edges > screenHeight:
            if ypointer >= 0 and self['relmouse'] in ('both', 'y'):
                y = ypointer
            else:
                y = toprel + widget.winfo_rooty()
            y = y - self._label.winfo_reqheight() - self['yoffset'] - edges

        Pmw.setgeometryanddeiconify(self, '+%d+%d' % (x, y))

######################################################################
### File: PmwButtonBox.py
# Based on iwidgets2.2.0/buttonbox.itk code.

import types
import tkinter
import Pmw

class ButtonBox(Pmw.MegaWidget):
    def __init__(self, parent = None, **kw):

        # Define the megawidget options.
        
        optiondefs = (
            ('labelmargin',       0,              INITOPT),
            ('labelpos',          None,           INITOPT),
            ('orient',            'horizontal',   INITOPT),
            ('padx',              3,              INITOPT),
            ('pady',              3,              INITOPT),
        )
        self.defineoptions(kw, optiondefs, dynamicGroups = ('Button',))

        # Initialise the base class (after defining the options).
        Pmw.MegaWidget.__init__(self, parent)

        # Create the components.
        interior = self.interior()
        if self['labelpos'] is None:
            self._buttonBoxFrame = self._hull
            columnOrRow = 0
        else:
            self._buttonBoxFrame = self.createcomponent('frame',
                    (), None,
                    tkinter.Frame, (interior,))
            self._buttonBoxFrame.grid(column=2, row=2, sticky='nsew')
            columnOrRow = 2

            self.createlabel(interior)

        orient = self['orient']
        if orient == 'horizontal':
            interior.grid_columnconfigure(columnOrRow, weight = 1)
        elif orient == 'vertical':
            interior.grid_rowconfigure(columnOrRow, weight = 1)
        else:
            raise ValueError('bad orient option ' + repr(orient) + \
                ': must be either \'horizontal\' or \'vertical\'')

        # Initialise instance variables.

        # List of tuples describing the buttons:
        #   - name
        #   - button widget
        self._buttonList = []

        # The index of the default button.
        self._defaultButton = None

        self._timerId = None

        # Check keywords and initialise options.
        self.initialiseoptions()

    def destroy(self):
        if self._timerId:
            self.after_cancel(self._timerId)
            self._timerId = None
        Pmw.MegaWidget.destroy(self)

    def numbuttons(self):
        return len(self._buttonList)

    def index(self, index, forInsert = 0):
        listLength = len(self._buttonList)
        if type(index) == int:
            if forInsert and index <= listLength:
                return index
            elif not forInsert and index < listLength:
                return index
            else:
                raise ValueError('index "%s" is out of range' % index)
        elif index is Pmw.END:
            if forInsert:
                return listLength
            elif listLength > 0:
                return listLength - 1
            else:
                raise ValueError('ButtonBox has no buttons')
        elif index is Pmw.DEFAULT:
            if self._defaultButton is not None:
                return self._defaultButton
            raise ValueError('ButtonBox has no default')
        else:
            names = [t[0] for t in self._buttonList]
            if index in names:
                return names.index(index)
            validValues = 'a name, a number, Pmw.END or Pmw.DEFAULT'
            raise ValueError('bad index "%s": must be %s' % (index, validValues))

    def insert(self, componentName, beforeComponent = 0, **kw):
        if componentName in self.components():
            raise ValueError('button "%s" already exists' % componentName)
        if 'text' not in kw:
            kw['text'] = componentName
        kw['default'] = 'normal'
        button = self.createcomponent(*(componentName,
                (), 'Button',
                tkinter.Button, (self._buttonBoxFrame,)), **kw)

        index = self.index(beforeComponent, 1)
        horizontal = self['orient'] == 'horizontal'
        numButtons = len(self._buttonList)

        # Shift buttons up one position.
        for i in range(numButtons - 1, index - 1, -1):
            widget = self._buttonList[i][1]
            pos = i * 2 + 3
            if horizontal:
                widget.grid(column = pos, row = 0)
            else:
                widget.grid(column = 0, row = pos)

        # Display the new button.
        if horizontal:
            button.grid(column = index * 2 + 1, row = 0, sticky = 'ew',
                    padx = self['padx'], pady = self['pady'])
            self._buttonBoxFrame.grid_columnconfigure(
                    numButtons * 2 + 2, weight = 1)
        else:
            button.grid(column = 0, row = index * 2 + 1, sticky = 'ew',
                    padx = self['padx'], pady = self['pady'])
            self._buttonBoxFrame.grid_rowconfigure(
                    numButtons * 2 + 2, weight = 1)
        self._buttonList.insert(index, (componentName, button))

        return button

    def add(self, componentName, **kw):
        return self.insert(*(componentName, len(self._buttonList)), **kw)

    def delete(self, index):
        index = self.index(index)
        (name, widget) = self._buttonList[index]
        widget.grid_forget()
        self.destroycomponent(name)

        numButtons = len(self._buttonList)

        # Shift buttons down one position.
        horizontal = self['orient'] == 'horizontal'
        for i in range(index + 1, numButtons):
            widget = self._buttonList[i][1]
            pos = i * 2 - 1
            if horizontal:
                widget.grid(column = pos, row = 0)
            else:
                widget.grid(column = 0, row = pos)

        if horizontal:
            self._buttonBoxFrame.grid_columnconfigure(numButtons * 2 - 1,
                    minsize = 0)
            self._buttonBoxFrame.grid_columnconfigure(numButtons * 2, weight = 0)
        else:
            self._buttonBoxFrame.grid_rowconfigure(numButtons * 2, weight = 0)
        del self._buttonList[index]

    def setdefault(self, index):
        # Turn off the default ring around the current default button.
        if self._defaultButton is not None:
            button = self._buttonList[self._defaultButton][1]
            button.configure(default = 'normal')
            self._defaultButton = None

        # Turn on the default ring around the new default button.
        if index is not None:
            index = self.index(index)
            self._defaultButton = index
            button = self._buttonList[index][1]
            button.configure(default = 'active')

    def invoke(self, index = Pmw.DEFAULT, noFlash = 0):
        # Invoke the callback associated with the *index* button.  If
        # *noFlash* is not set, flash the button to indicate to the
        # user that something happened.

        button = self._buttonList[self.index(index)][1]
        if not noFlash:
            state = button.cget('state')
            relief = button.cget('relief')
            button.configure(state = 'active', relief = 'sunken')
            self.update_idletasks()
            self.after(100)
            button.configure(state = state, relief = relief)
        return button.invoke()

    def button(self, buttonIndex):
        return self._buttonList[self.index(buttonIndex)][1]

    def alignbuttons(self, when = 'later'):
        if when == 'later':
            if not self._timerId:
                self._timerId = self.after_idle(self.alignbuttons, 'now')
            return
        self.update_idletasks()
        self._timerId = None

        # Determine the width of the maximum length button.
        max = 0
        horizontal = (self['orient'] == 'horizontal')
        for index in range(len(self._buttonList)):
            gridIndex = index * 2 + 1
            if horizontal:
                width = self._buttonBoxFrame.grid_bbox(gridIndex, 0)[2]
            else:
                width = self._buttonBoxFrame.grid_bbox(0, gridIndex)[2]
            if width > max:
                max = width

        # Set the width of all the buttons to be the same.
        if horizontal:
            for index in range(len(self._buttonList)):
                self._buttonBoxFrame.grid_columnconfigure(index * 2 + 1,
                        minsize = max)
        else:
            self._buttonBoxFrame.grid_columnconfigure(0, minsize = max)

######################################################################
### File: PmwEntryField.py
# Based on iwidgets2.2.0/entryfield.itk code.

import re
import string
import types
import tkinter
import Pmw
import collections

# Possible return values of validation functions.
OK = 1
ERROR = 0
PARTIAL = -1

class EntryField(Pmw.MegaWidget):
    _classBindingsDefinedFor = 0

    def __init__(self, parent = None, **kw):

        # Define the megawidget options.
        
        optiondefs = (
            ('command',           None,        None),
            ('errorbackground',   'pink',      None),
            ('invalidcommand',    self.bell,   None),
            ('labelmargin',       0,           INITOPT),
            ('labelpos',          None,        INITOPT),
            ('modifiedcommand',   None,        None),
            ('sticky',            'ew',        INITOPT),
            ('validate',          None,        self._validate),
            ('extravalidators',   {},          None),
            ('value',             '',          INITOPT),
        )
        self.defineoptions(kw, optiondefs)

        # Initialise the base class (after defining the options).
        Pmw.MegaWidget.__init__(self, parent)

        # Create the components.
        interior = self.interior()
        self._entryFieldEntry = self.createcomponent('entry',
                (), None,
                tkinter.Entry, (interior,))
        self._entryFieldEntry.grid(column=2, row=2, sticky=self['sticky'])
        if self['value'] != '':
            self.__setEntry(self['value'])
        interior.grid_columnconfigure(2, weight=1)
        interior.grid_rowconfigure(2, weight=1)

        self.createlabel(interior)

        # Initialise instance variables.

        self.normalBackground = None
        self._previousText = None

        # Initialise instance.

        _registerEntryField(self._entryFieldEntry, self)

        # Establish the special class bindings if not already done.
        # Also create bindings if the Tkinter default interpreter has
        # changed.  Use Tkinter._default_root to create class
        # bindings, so that a reference to root is created by
        # bind_class rather than a reference to self, which would
        # prevent object cleanup.
        if EntryField._classBindingsDefinedFor != tkinter._default_root:
            tagList = self._entryFieldEntry.bindtags()
            root  = tkinter._default_root

            allSequences = {}
            for tag in tagList:

                sequences = root.bind_class(tag)
                if type(sequences) is str:
                    # In old versions of Tkinter, bind_class returns a string
                    sequences = root.tk.splitlist(sequences)

                for sequence in sequences:
                    allSequences[sequence] = None
            for sequence in list(allSequences.keys()):
                root.bind_class('EntryFieldPre', sequence, _preProcess)
                root.bind_class('EntryFieldPost', sequence, _postProcess)

            EntryField._classBindingsDefinedFor = root

        self._entryFieldEntry.bindtags(('EntryFieldPre',) +
                self._entryFieldEntry.bindtags() + ('EntryFieldPost',))
        self._entryFieldEntry.bind('<Return>', self._executeCommand)

        # Check keywords and initialise options.
        self.initialiseoptions()

    def destroy(self):
        _deregisterEntryField(self._entryFieldEntry)
        Pmw.MegaWidget.destroy(self)

    def _getValidatorFunc(self, validator, index):
        # Search the extra and standard validator lists for the
        # given 'validator'.  If 'validator' is an alias, then
        # continue the search using the alias.  Make sure that
        # self-referencial aliases do not cause infinite loops.

        extraValidators = self['extravalidators']
        traversedValidators = []

        while 1:
            traversedValidators.append(validator)
            if validator in extraValidators:
                validator = extraValidators[validator][index]
            elif validator in _standardValidators:
                validator = _standardValidators[validator][index]
            else:
                return validator
            if validator in traversedValidators:
                return validator

    def _validate(self):
        dictio = {
            'validator' : None,
            'min' : None,
            'max' : None,
            'minstrict' : 1,
            'maxstrict' : 1,
        }
        opt = self['validate']
        if type(opt) is dict:
            dictio.update(opt)
        else:
            dictio['validator'] = opt

        # Look up validator maps and replace 'validator' field with
        # the corresponding function.
        validator = dictio['validator']
        valFunction = self._getValidatorFunc(validator, 0)
        self._checkValidateFunction(valFunction, 'validate', validator)
        dictio['validator'] = valFunction

        # Look up validator maps and replace 'stringtovalue' field
        # with the corresponding function.
        if 'stringtovalue' in dictio:
            stringtovalue = dictio['stringtovalue']
            strFunction = self._getValidatorFunc(stringtovalue, 1)
            self._checkValidateFunction(
                    strFunction, 'stringtovalue', stringtovalue)
        else:
            strFunction = self._getValidatorFunc(validator, 1)
            if strFunction == validator:
                strFunction = len
        dictio['stringtovalue'] = strFunction

        self._validationInfo = dictio
        args = dictio.copy()
        del args['validator']
        del args['min']
        del args['max']
        del args['minstrict']
        del args['maxstrict']
        del args['stringtovalue']
        self._validationArgs = args
        self._previousText = None

        if type(dictio['min']) is str and strFunction is not None:
            dictio['min'] = strFunction(*(dictio['min'],), **args)
        if type(dictio['max']) is str and strFunction is not None:
            dictio['max'] = strFunction(*(dictio['max'],), **args)

        self._checkValidity()

    def _checkValidateFunction(self, function, option, validator):
        # Raise an error if 'function' is not a function or None.

        if function is not None and not hasattr(function, '__call__'):
            extraValidators = self['extravalidators']
            extra = list(extraValidators.keys())
            extra.sort()
            extra = tuple(extra)
            standard = list(_standardValidators.keys())
            standard.sort()
            standard = tuple(standard)
            msg = 'bad %s value "%s":  must be a function or one of ' \
                'the standard validators %s or extra validators %s'
            raise ValueError(msg % (option, validator, standard, extra))

    def _executeCommand(self, event = None):
        cmd = self['command']
        if hasattr(cmd, '__call__'):
            if event is None:
                # Return result of command for invoke() method.
                return cmd()
            else:
                cmd()

    def _preProcess(self):

        self._previousText = self._entryFieldEntry.get()
        self._previousICursor = self._entryFieldEntry.index('insert')
        self._previousXview = self._entryFieldEntry.index('@0')
        if self._entryFieldEntry.selection_present():
            self._previousSel= (self._entryFieldEntry.index('sel.first'),
                self._entryFieldEntry.index('sel.last'))
        else:
            self._previousSel = None

    def _postProcess(self):

        # No need to check if text has not changed.
        previousText = self._previousText
        if previousText == self._entryFieldEntry.get():
            return self.valid()

        valid = self._checkValidity()
        if self.hulldestroyed():
            # The invalidcommand called by _checkValidity() destroyed us.
            return valid

        cmd = self['modifiedcommand']
        if hasattr(cmd, '__call__') and previousText != self._entryFieldEntry.get():
            cmd()
        return valid

    def checkentry(self):
        # If there is a variable specified by the entry_textvariable
        # option, checkentry() should be called after the set() method
        # of the variable is called.

        self._previousText = None
        return self._postProcess()

    def _getValidity(self):
        text = self._entryFieldEntry.get()
        dictio = self._validationInfo
        args = self._validationArgs

        if dictio['validator'] is not None:
            status = dictio['validator'](*(text,), **args)
            if status != OK:
                return status

        # Check for out of (min, max) range.
        if dictio['stringtovalue'] is not None:
            min = dictio['min']
            max = dictio['max']
            if min is None and max is None:
                return OK
            val = dictio['stringtovalue'](*(text,), **args)
            if min is not None and val < min:
                if dictio['minstrict']:
                    return ERROR
                else:
                    return PARTIAL
            if max is not None and val > max:
                if dictio['maxstrict']:
                    return ERROR
                else:
                    return PARTIAL
        return OK

    def _checkValidity(self):
        valid = self._getValidity()
        oldValidity = valid

        if valid == ERROR:
            # The entry is invalid.
            cmd = self['invalidcommand']
            if hasattr(cmd, '__call__'):
                cmd()
            if self.hulldestroyed():
                # The invalidcommand destroyed us.
                return oldValidity

            # Restore the entry to its previous value.
            if self._previousText is not None:
                self.__setEntry(self._previousText)
                self._entryFieldEntry.icursor(self._previousICursor)
                self._entryFieldEntry.xview(self._previousXview)
                if self._previousSel is not None:
                    self._entryFieldEntry.selection_range(self._previousSel[0],
                        self._previousSel[1])

                # Check if the saved text is valid as well.
                valid = self._getValidity()

        self._valid = valid

        if self.hulldestroyed():
            # The validator or stringtovalue commands called by
            # _checkValidity() destroyed us.
            return oldValidity

        if valid == OK:
            if self.normalBackground is not None:
                self._entryFieldEntry.configure(
                        background = self.normalBackground)
                self.normalBackground = None
        else:
            if self.normalBackground is None:
                self.normalBackground = self._entryFieldEntry.cget('background')
                self._entryFieldEntry.configure(
                        background = self['errorbackground'])

        return oldValidity

    def invoke(self):
        return self._executeCommand()

    def valid(self):
        return self._valid == OK

    def clear(self):
        self.setentry('')

    def __setEntry(self, text):
        oldState = str(self._entryFieldEntry.cget('state'))
        if oldState != 'normal':
            self._entryFieldEntry.configure(state='normal')
        self._entryFieldEntry.delete(0, 'end')
        self._entryFieldEntry.insert(0, text)
        if oldState != 'normal':
            self._entryFieldEntry.configure(state=oldState)

    def setentry(self, text):
        self._preProcess()
        self.__setEntry(text)
        return self._postProcess()

    def getvalue(self):
        return self._entryFieldEntry.get()

    def setvalue(self, text):
        return self.setentry(text)

Pmw.forwardmethods(EntryField, tkinter.Entry, '_entryFieldEntry')

# ======================================================================


# Entry field validation functions

_numericregex = re.compile('^[0-9]*$')
_alphabeticregex = re.compile('^[a-z]*$', re.IGNORECASE)
_alphanumericregex = re.compile('^[0-9a-z]*$', re.IGNORECASE)

def numericvalidator(text):
    if text == '':
        return PARTIAL
    else:
        if _numericregex.match(text) is None:
            return ERROR
        else:
            return OK

def integervalidator(text):
    if text in ('', '-', '+'):
        return PARTIAL
    try:
        int(text)
        return OK
    except ValueError:
        return ERROR

def alphabeticvalidator(text):
    if _alphabeticregex.match(text) is None:
        return ERROR
    else:
        return OK

def alphanumericvalidator(text):
    if _alphanumericregex.match(text) is None:
        return ERROR
    else:
        return OK

def hexadecimalvalidator(text):
    if text in ('', '0x', '0X', '+', '+0x', '+0X', '-', '-0x', '-0X'):
        return PARTIAL
    try:
        int(text, 16)
        return OK
    except ValueError:
        return ERROR

def realvalidator(text, separator = '.'):
    if separator != '.':
        if text.find('.') >= 0:
            return ERROR
        index = text.find(separator)
        if index >= 0:
            text = text[:index] + '.' + text[index + 1:]
    try:
        float(text)
        return OK
    except ValueError:
        # Check if the string could be made valid by appending a digit
        # eg ('-', '+', '.', '-.', '+.', '1.23e', '1E-').
        if len(text) == 0:
            return PARTIAL
        if text[-1] in string.digits:
            return ERROR
        try:
            float(text + '0')
            return PARTIAL
        except ValueError:
            return ERROR

def timevalidator(text, separator = ':'):
    try:
        Pmw.timestringtoseconds(text, separator)
        return OK
    except ValueError:
        if len(text) > 0 and text[0] in ('+', '-'):
            text = text[1:]
        if re.search('[^0-9' + separator + ']', text) is not None:
            return ERROR
        return PARTIAL

def datevalidator(text, fmt = 'ymd', separator = '/'):
    try:
        Pmw.datestringtojdn(text, fmt, separator)
        return OK
    except ValueError:
        if re.search('[^0-9' + separator + ']', text) is not None:
            return ERROR
        return PARTIAL

_standardValidators = {
    'numeric'      : (numericvalidator,      int),
    'integer'      : (integervalidator,      int),
    'hexadecimal'  : (hexadecimalvalidator,  lambda s: int(s, 16)),
    'real'         : (realvalidator,         Pmw.stringtoreal),
    'alphabetic'   : (alphabeticvalidator,   len),
    'alphanumeric' : (alphanumericvalidator, len),
    'time'         : (timevalidator,         Pmw.timestringtoseconds),
    'date'         : (datevalidator,         Pmw.datestringtojdn),
}

_entryCache = {}

def _registerEntryField(entry, entryField):
    # Register an EntryField widget for an Entry widget

    _entryCache[entry] = entryField

def _deregisterEntryField(entry):
    # Deregister an Entry widget
    del _entryCache[entry]

def _preProcess(event):
    # Forward preprocess events for an Entry to it's EntryField

    _entryCache[event.widget]._preProcess()

def _postProcess(event):
    # Forward postprocess events for an Entry to it's EntryField

    # The function specified by the 'command' option may have destroyed
    # the megawidget in a binding earlier in bindtags, so need to check.
    if event.widget in _entryCache:
        _entryCache[event.widget]._postProcess()

######################################################################
### File: PmwGroup.py
import string
import tkinter
import Pmw

def aligngrouptags(groups):
    # Adjust the y position of the tags in /groups/ so that they all
    # have the height of the highest tag.

    maxTagHeight = 0
    for group in groups:
        if group._tag is None:
            height = (int(str(group._ring.cget('borderwidth'))) +
                    int(str(group._ring.cget('highlightthickness'))))
        else:
            height = group._tag.winfo_reqheight()
        if maxTagHeight < height:
            maxTagHeight = height

    for group in groups:
        ringBorder = (int(str(group._ring.cget('borderwidth'))) +
                int(str(group._ring.cget('highlightthickness'))))
        topBorder = maxTagHeight / 2 - ringBorder / 2
        group._hull.grid_rowconfigure(0, minsize = topBorder)
        group._ring.grid_rowconfigure(0,
                minsize = maxTagHeight - topBorder - ringBorder)
        if group._tag is not None:
            group._tag.place(y = maxTagHeight / 2)

class Group( Pmw.MegaWidget ):
    def __init__(self, parent = None, **kw):

        # Define the megawidget options.

        
        optiondefs = (
            ('collapsedheight',  6,         INITOPT),
            ('collapsedwidth',   20,        INITOPT),
            ('ring_borderwidth', 2,         None),
            ('ring_relief',      'groove',  None),
            ('tagindent',        10,        INITOPT),
        )
        self.defineoptions(kw, optiondefs)

        # Initialise the base class (after defining the options).
        Pmw.MegaWidget.__init__(self, parent)

        # Create the components.
        interior = Pmw.MegaWidget.interior(self)

        self._ring = self.createcomponent(
            'ring',
            (), None,
            tkinter.Frame, (interior,),
            )

        self._groupChildSite = self.createcomponent(
            'groupchildsite',
            (), None,
            tkinter.Frame, (self._ring,)
            )

        self._tag = self.createcomponent(
            'tag',
            (), None,
            tkinter.Label, (interior,),
            )

        ringBorder = (int(str(self._ring.cget('borderwidth'))) +
                int(str(self._ring.cget('highlightthickness'))))
        if self._tag is None:
            tagHeight = ringBorder
        else:
            tagHeight = self._tag.winfo_reqheight()
            self._tag.place(
                    x = ringBorder + self['tagindent'],
                    y = tagHeight / 2,
                    anchor = 'w')

        topBorder = tagHeight / 2 - ringBorder / 2
        self._ring.grid(column = 0, row = 1, sticky = 'nsew')
        interior.grid_columnconfigure(0, weight = 1)
        interior.grid_rowconfigure(1, weight = 1)
        interior.grid_rowconfigure(0, minsize = topBorder)

        self._groupChildSite.grid(column = 0, row = 1, sticky = 'nsew')
        self._ring.grid_columnconfigure(0, weight = 1)
        self._ring.grid_rowconfigure(1, weight = 1)
        self._ring.grid_rowconfigure(0,
                minsize = tagHeight - topBorder - ringBorder)

        self.showing = 1

        # Check keywords and initialise options.
        self.initialiseoptions()

    def toggle(self):
        if self.showing:
            self.collapse()
        else:
            self.expand()
        self.showing = not self.showing

    def expand(self):
        self._groupChildSite.grid(column = 0, row = 1, sticky = 'nsew')

    def collapse(self):
        self._groupChildSite.grid_forget()
        if self._tag is None:
            tagHeight = 0
        else:
            tagHeight = self._tag.winfo_reqheight()
            tagWidth = self._tag.winfo_reqwidth()
        self._ring.configure(height=(tagHeight / 2) + self['collapsedheight'],
                width = tagWidth + self['collapsedwidth'])

    def interior(self):
        return self._groupChildSite

######################################################################
### File: PmwScrolledListBox.py
# Based on iwidgets2.2.0/scrolledlistbox.itk code.

import types
import tkinter
import Pmw
import collections

class ScrolledListBox(Pmw.MegaWidget):
    _classBindingsDefinedFor = 0

    def __init__(self, parent = None, **kw):

        # Define the megawidget options.
        
        optiondefs = (
            ('dblclickcommand',    None,            None),
            ('hscrollmode',        'dynamic',       self._hscrollMode),
            ('items',              (),              INITOPT),
            ('labelmargin',        0,               INITOPT),
            ('labelpos',           None,            INITOPT),
            ('scrollmargin',       2,               INITOPT),
            ('selectioncommand',   None,            None),
            ('usehullsize',        0,               INITOPT),
            ('vscrollmode',        'dynamic',       self._vscrollMode),
        )
        self.defineoptions(kw, optiondefs)

        # Initialise the base class (after defining the options).
        Pmw.MegaWidget.__init__(self, parent)

        # Create the components.
        interior = self.interior()

        if self['usehullsize']:
            interior.grid_propagate(0)

        # Create the listbox widget.
        self._listbox = self.createcomponent('listbox',
                (), None,
                tkinter.Listbox, (interior,))
        self._listbox.grid(row = 2, column = 2, sticky = 'news')
        interior.grid_rowconfigure(2, weight = 1, minsize = 0)
        interior.grid_columnconfigure(2, weight = 1, minsize = 0)

        # Create the horizontal scrollbar
        self._horizScrollbar = self.createcomponent('horizscrollbar',
                (), 'Scrollbar',
                tkinter.Scrollbar, (interior,),
                orient='horizontal',
                command=self._listbox.xview
        )

        # Create the vertical scrollbar
        self._vertScrollbar = self.createcomponent('vertscrollbar',
                (), 'Scrollbar',
                tkinter.Scrollbar, (interior,),
                orient='vertical',
                command=self._listbox.yview
        )

        self.createlabel(interior, childCols = 3, childRows = 3)

        # Add the items specified by the initialisation option.
        items = self['items']
        if type(items) != tuple:
            items = tuple(items)
        if len(items) > 0:
            self._listbox.insert(*('end',) + items)

        _registerScrolledList(self._listbox, self)

        # Establish the special class bindings if not already done.
        # Also create bindings if the Tkinter default interpreter has
        # changed.  Use Tkinter._default_root to create class
        # bindings, so that a reference to root is created by
        # bind_class rather than a reference to self, which would
        # prevent object cleanup.
        theTag = 'ScrolledListBoxTag'
        if ScrolledListBox._classBindingsDefinedFor != tkinter._default_root:
            root  = tkinter._default_root

            def doubleEvent(event):
                _handleEvent(event, 'double')
            def keyEvent(event):
                _handleEvent(event, 'key')
            def releaseEvent(event):
                _handleEvent(event, 'release')

            # Bind space and return keys and button 1 to the selectioncommand.
            root.bind_class(theTag, '<Key-space>', keyEvent)
            root.bind_class(theTag, '<Key-Return>', keyEvent)
            root.bind_class(theTag, '<ButtonRelease-1>', releaseEvent)

            # Bind double button 1 click to the dblclickcommand.
            root.bind_class(theTag, '<Double-ButtonRelease-1>', doubleEvent)

            ScrolledListBox._classBindingsDefinedFor = root

        bindtags = self._listbox.bindtags()
        self._listbox.bindtags(bindtags + (theTag,))

        # Initialise instance variables.
        self._horizScrollbarOn = 0
        self._vertScrollbarOn = 0
        self.scrollTimer = None
        self._scrollRecurse = 0
        self._horizScrollbarNeeded = 0
        self._vertScrollbarNeeded = 0

        # Check keywords and initialise options.
        self.initialiseoptions()

    def destroy(self):
        if self.scrollTimer is not None:
            self.after_cancel(self.scrollTimer)
            self.scrollTimer = None
        _deregisterScrolledList(self._listbox)
        Pmw.MegaWidget.destroy(self)

    # ======================================================================

    # Public methods.

    def clear(self):
        self.setlist(())

    def getcurselection(self):
        rtn = []
        for sel in self.curselection():
            rtn.append(self._listbox.get(sel))
        return tuple(rtn)

    def getvalue(self):
        return self.getcurselection()

    def setvalue(self, textOrList):
        self._listbox.selection_clear(0, 'end')
        listitems = list(self._listbox.get(0, 'end'))
        if type(textOrList) is str:
            if textOrList in listitems:
                self._listbox.selection_set(listitems.index(textOrList))
            else:
                raise ValueError('no such item "%s"' % textOrList)
        else:
            for item in textOrList:
                if item in listitems:
                    self._listbox.selection_set(listitems.index(item))
                else:
                    raise ValueError('no such item "%s"' % item)

    def setlist(self, items):
        self._listbox.delete(0, 'end')
        if len(items) > 0:
            if type(items) != tuple:
                items = tuple(items)
            self._listbox.insert(*(0,) + items)

    # Override Tkinter.Listbox get method, so that if it is called with
    # no arguments, return all list elements (consistent with other widgets).
    def get(self, first=None, last=None):
        if first is None:
            return self._listbox.get(0, 'end')
        else:
            return self._listbox.get(first, last)

    # ======================================================================

    # Configuration methods.

    def _hscrollMode(self):
        # The horizontal scroll mode has been configured.

        mode = self['hscrollmode']

        if mode == 'static':
            if not self._horizScrollbarOn:
                self._toggleHorizScrollbar()
        elif mode == 'dynamic':
            if self._horizScrollbarNeeded != self._horizScrollbarOn:
                self._toggleHorizScrollbar()
        elif mode == 'none':
            if self._horizScrollbarOn:
                self._toggleHorizScrollbar()
        else:
            message = 'bad hscrollmode option "%s": should be static, dynamic, or none' % mode
            raise ValueError(message)

        self._configureScrollCommands()

    def _vscrollMode(self):
        # The vertical scroll mode has been configured.

        mode = self['vscrollmode']

        if mode == 'static':
            if not self._vertScrollbarOn:
                self._toggleVertScrollbar()
        elif mode == 'dynamic':
            if self._vertScrollbarNeeded != self._vertScrollbarOn:
                self._toggleVertScrollbar()
        elif mode == 'none':
            if self._vertScrollbarOn:
                self._toggleVertScrollbar()
        else:
            message = 'bad vscrollmode option "%s": should be static, dynamic, or none' % mode
            raise ValueError(message)

        self._configureScrollCommands()

    # ======================================================================

    # Private methods.

    def _configureScrollCommands(self):
        # If both scrollmodes are not dynamic we can save a lot of
        # time by not having to create an idle job to handle the
        # scroll commands.

        # Clean up previous scroll commands to prevent memory leak.
        tclCommandName = str(self._listbox.cget('xscrollcommand'))
        if tclCommandName != '':
            self._listbox.deletecommand(tclCommandName)
        tclCommandName = str(self._listbox.cget('yscrollcommand'))
        if tclCommandName != '':
            self._listbox.deletecommand(tclCommandName)

        if self['hscrollmode'] == self['vscrollmode'] == 'dynamic':
            self._listbox.configure(
                    xscrollcommand=self._scrollBothLater,
                    yscrollcommand=self._scrollBothLater
            )
        else:
            self._listbox.configure(
                    xscrollcommand=self._scrollXNow,
                    yscrollcommand=self._scrollYNow
            )

    def _scrollXNow(self, first, last):
        self._horizScrollbar.set(first, last)
        self._horizScrollbarNeeded = ((first, last) != ('0', '1'))

        if self['hscrollmode'] == 'dynamic':
            if self._horizScrollbarNeeded != self._horizScrollbarOn:
                self._toggleHorizScrollbar()

    def _scrollYNow(self, first, last):
        self._vertScrollbar.set(first, last)
        self._vertScrollbarNeeded = ((first, last) != ('0', '1'))

        if self['vscrollmode'] == 'dynamic':
            if self._vertScrollbarNeeded != self._vertScrollbarOn:
                self._toggleVertScrollbar()

    def _scrollBothLater(self, first, last):
        # Called by the listbox to set the horizontal or vertical
        # scrollbar when it has scrolled or changed size or contents.

        if self.scrollTimer is None:
            self.scrollTimer = self.after_idle(self._scrollBothNow)

    def _scrollBothNow(self):
        # This performs the function of _scrollXNow and _scrollYNow.
        # If one is changed, the other should be updated to match.
        self.scrollTimer = None

        # Call update_idletasks to make sure that the containing frame
        # has been resized before we attempt to set the scrollbars.
        # Otherwise the scrollbars may be mapped/unmapped continuously.
        self._scrollRecurse = self._scrollRecurse + 1
        self.update_idletasks()
        self._scrollRecurse = self._scrollRecurse - 1
        if self._scrollRecurse != 0:
            return

        xview = self._listbox.xview()
        yview = self._listbox.yview()
        self._horizScrollbar.set(xview[0], xview[1])
        self._vertScrollbar.set(yview[0], yview[1])

        self._horizScrollbarNeeded = (xview != (0.0, 1.0))
        self._vertScrollbarNeeded = (yview != (0.0, 1.0))

        # If both horizontal and vertical scrollmodes are dynamic and
        # currently only one scrollbar is mapped and both should be
        # toggled, then unmap the mapped scrollbar.  This prevents a
        # continuous mapping and unmapping of the scrollbars.
        if (self['hscrollmode'] == self['vscrollmode'] == 'dynamic' and
                self._horizScrollbarNeeded != self._horizScrollbarOn and
                self._vertScrollbarNeeded != self._vertScrollbarOn and
                self._vertScrollbarOn != self._horizScrollbarOn):
            if self._horizScrollbarOn:
                self._toggleHorizScrollbar()
            else:
                self._toggleVertScrollbar()
            return

        if self['hscrollmode'] == 'dynamic':
            if self._horizScrollbarNeeded != self._horizScrollbarOn:
                self._toggleHorizScrollbar()

        if self['vscrollmode'] == 'dynamic':
            if self._vertScrollbarNeeded != self._vertScrollbarOn:
                self._toggleVertScrollbar()

    def _toggleHorizScrollbar(self):

        self._horizScrollbarOn = not self._horizScrollbarOn

        interior = self.interior()
        if self._horizScrollbarOn:
            self._horizScrollbar.grid(row = 4, column = 2, sticky = 'news')
            interior.grid_rowconfigure(3, minsize = self['scrollmargin'])
        else:
            self._horizScrollbar.grid_forget()
            interior.grid_rowconfigure(3, minsize = 0)

    def _toggleVertScrollbar(self):

        self._vertScrollbarOn = not self._vertScrollbarOn

        interior = self.interior()
        if self._vertScrollbarOn:
            self._vertScrollbar.grid(row = 2, column = 4, sticky = 'news')
            interior.grid_columnconfigure(3, minsize = self['scrollmargin'])
        else:
            self._vertScrollbar.grid_forget()
            interior.grid_columnconfigure(3, minsize = 0)

    def _handleEvent(self, event, eventType):
        if eventType == 'double':
            command = self['dblclickcommand']
        elif eventType == 'key':
            command = self['selectioncommand']
        else: #eventType == 'release'
            # Do not execute the command if the mouse was released
            # outside the listbox.
            if (event.x < 0 or self._listbox.winfo_width() <= event.x or
                    event.y < 0 or self._listbox.winfo_height() <= event.y):
                return

            command = self['selectioncommand']

        if hasattr(command, '__call__'):
            command()

    # Need to explicitly forward this to override the stupid
    # (grid_)size method inherited from Tkinter.Frame.Grid.
    def size(self):
        return self._listbox.size()

    # Need to explicitly forward this to override the stupid
    # (grid_)bbox method inherited from Tkinter.Frame.Grid.
    def bbox(self, index):
        return self._listbox.bbox(index)

Pmw.forwardmethods(ScrolledListBox, tkinter.Listbox, '_listbox')

# ======================================================================

_listboxCache = {}

def _registerScrolledList(listbox, scrolledList):
    # Register an ScrolledList widget for a Listbox widget

    _listboxCache[listbox] = scrolledList

def _deregisterScrolledList(listbox):
    # Deregister a Listbox widget
    del _listboxCache[listbox]

def _handleEvent(event, eventType):
    # Forward events for a Listbox to it's ScrolledListBox

    # A binding earlier in the bindtags list may have destroyed the
    # megawidget, so need to check.
    if event.widget in _listboxCache:
        _listboxCache[event.widget]._handleEvent(event, eventType)

######################################################################
### File: PmwComboBox.py
# Based on iwidgets2.2.0/combobox.itk code.

import os
import string
import types
import tkinter
import Pmw
import collections

class ComboBox(Pmw.MegaWidget):
    def __init__(self, parent = None, **kw):

        # Define the megawidget options.
        
        optiondefs = (
            ('autoclear',          0,          INITOPT),
            ('buttonaspect',       1.0,        INITOPT),
            ('dropdown',           1,          INITOPT),
            ('fliparrow',          0,          INITOPT),
            ('history',            1,          INITOPT),
            ('labelmargin',        0,          INITOPT),
            ('labelpos',           None,       INITOPT),
            ('listheight',         200,        INITOPT),
            ('selectioncommand',   None,       None),
            ('sticky',            'ew',        INITOPT),
            ('unique',             1,          INITOPT),
        )
        self.defineoptions(kw, optiondefs)

        # Initialise the base class (after defining the options).
        Pmw.MegaWidget.__init__(self, parent)

        # Create the components.
        interior = self.interior()

        self._entryfield = self.createcomponent('entryfield',
                (('entry', 'entryfield_entry'),), None,
                Pmw.EntryField, (interior,))
        self._entryfield.grid(column=2, row=2, sticky=self['sticky'])
        interior.grid_columnconfigure(2, weight = 1)
        self._entryWidget = self._entryfield.component('entry')

        if self['dropdown']:
            self._isPosted = 0
            interior.grid_rowconfigure(2, weight = 1)

            # Create the arrow button.
            self._arrowBtn = self.createcomponent('arrowbutton',
                    (), None,
                    tkinter.Canvas, (interior,), borderwidth = 2,
                    relief = 'raised',
                    width = 16, height = 16)
            if 'n' in self['sticky']:
                sticky = 'n'
            else:
                sticky = ''
            if 's' in self['sticky']:
                sticky = sticky + 's'
            self._arrowBtn.grid(column=3, row=2, sticky = sticky)
            self._arrowRelief = self._arrowBtn.cget('relief')

            # Create the label.
            self.createlabel(interior, childCols=2)

            # Create the dropdown window.
            self._popup = self.createcomponent('popup',
                    (), None,
                    tkinter.Toplevel, (interior,))
            self._popup.withdraw()
            self._popup.overrideredirect(1)

            # Create the scrolled listbox inside the dropdown window.
            self._list = self.createcomponent('scrolledlist',
                    (('listbox', 'scrolledlist_listbox'),), None,
                    Pmw.ScrolledListBox, (self._popup,),
                    hull_borderwidth = 2,
                    hull_relief = 'raised',
                    hull_height = self['listheight'],
                    usehullsize = 1,
                    listbox_exportselection = 0)
            self._list.pack(expand=1, fill='both')
            self.__listbox = self._list.component('listbox')

            # Bind events to the arrow button.
            self._arrowBtn.bind('<1>', self._postList)
            self._arrowBtn.bind('<Configure>', self._drawArrow)
            self._arrowBtn.bind('<3>', self._next)
            self._arrowBtn.bind('<Shift-3>', self._previous)
            self._arrowBtn.bind('<Down>', self._next)
            self._arrowBtn.bind('<Up>', self._previous)
            self._arrowBtn.bind('<Control-n>', self._next)
            self._arrowBtn.bind('<Control-p>', self._previous)
            self._arrowBtn.bind('<Shift-Down>', self._postList)
            self._arrowBtn.bind('<Shift-Up>', self._postList)
            self._arrowBtn.bind('<F34>', self._postList)
            self._arrowBtn.bind('<F28>', self._postList)
            self._arrowBtn.bind('<space>', self._postList)

            # Bind events to the dropdown window.
            self._popup.bind('<Escape>', self._unpostList)
            self._popup.bind('<space>', self._selectUnpost)
            self._popup.bind('<Return>', self._selectUnpost)
            self._popup.bind('<ButtonRelease-1>', self._dropdownBtnRelease)
            self._popup.bind('<ButtonPress-1>', self._unpostOnNextRelease)

            # Bind events to the Tk listbox.
            self.__listbox.bind('<Enter>', self._unpostOnNextRelease)

            # Bind events to the Tk entry widget.
            self._entryWidget.bind('<Configure>', self._resizeArrow)
            self._entryWidget.bind('<Shift-Down>', self._postList)
            self._entryWidget.bind('<Shift-Up>', self._postList)
            self._entryWidget.bind('<F34>', self._postList)
            self._entryWidget.bind('<F28>', self._postList)

            # Need to unpost the popup if the entryfield is unmapped (eg:
            # its toplevel window is withdrawn) while the popup list is
            # displayed.
            self._entryWidget.bind('<Unmap>', self._unpostList)

        else:
            # Create the scrolled listbox below the entry field.
            self._list = self.createcomponent('scrolledlist',
                    (('listbox', 'scrolledlist_listbox'),), None,
                    Pmw.ScrolledListBox, (interior,),
                    selectioncommand = self._selectCmd)
            self._list.grid(column=2, row=3, sticky='nsew')
            self.__listbox = self._list.component('listbox')

            # The scrolled listbox should expand vertically.
            interior.grid_rowconfigure(3, weight = 1)

            # Create the label.
            self.createlabel(interior, childRows=2)

        self._entryWidget.bind('<Down>', self._next)
        self._entryWidget.bind('<Up>', self._previous)
        self._entryWidget.bind('<Control-n>', self._next)
        self._entryWidget.bind('<Control-p>', self._previous)
        self.__listbox.bind('<Control-n>', self._next)
        self.__listbox.bind('<Control-p>', self._previous)

        if self['history']:
            self._entryfield.configure(command=self._addHistory)

        # Check keywords and initialise options.
        self.initialiseoptions()

    def destroy(self):
        if self['dropdown'] and self._isPosted:
            Pmw.popgrab(self._popup)
        Pmw.MegaWidget.destroy(self)

    #======================================================================

    # Public methods

    def get(self, first = None, last=None):
        if first is None:
            return self._entryWidget.get()
        else:
            return self._list.get(first, last)

    def invoke(self):
        if self['dropdown']:
            self._postList()
        else:
            return self._selectCmd()

    def selectitem(self, index, setentry=1):
        if type(index) is str:
            text = index
            items = self._list.get(0, 'end')
            if text in items:
                index = list(items).index(text)
            else:
                raise IndexError('index "%s" not found' % text)
        elif setentry:
            text = self._list.get(0, 'end')[index]

        self._list.select_clear(0, 'end')
        self._list.select_set(index, index)
        self._list.activate(index)
        self.see(index)
        if setentry:
            self._entryfield.setentry(text)

    # Need to explicitly forward this to override the stupid
    # (grid_)size method inherited from Tkinter.Frame.Grid.
    def size(self):
        return self._list.size()

    # Need to explicitly forward this to override the stupid
    # (grid_)bbox method inherited from Tkinter.Frame.Grid.
    def bbox(self, index):
        return self._list.bbox(index)

    def clear(self):
        self._entryfield.clear()
        self._list.clear()

    #======================================================================

    # Private methods for both dropdown and simple comboboxes.

    def _addHistory(self):
        input = self._entryWidget.get()

        if input != '':
            index = None
            if self['unique']:
                # If item is already in list, select it and return.
                items = self._list.get(0, 'end')
                if input in items:
                    index = list(items).index(input)

            if index is None:
                index = self._list.index('end')
                self._list.insert('end', input)

            self.selectitem(index)
            if self['autoclear']:
                self._entryWidget.delete(0, 'end')

            # Execute the selectioncommand on the new entry.
            self._selectCmd()

    def _next(self, event):
        size = self.size()
        if size <= 1:
            return

        cursels = self.curselection()

        if len(cursels) == 0:
            index = 0
        else:
            index = int(cursels[0])
            if index == size - 1:
                index = 0
            else:
                index = index + 1

        self.selectitem(index)

    def _previous(self, event):
        size = self.size()
        if size <= 1:
            return

        cursels = self.curselection()

        if len(cursels) == 0:
            index = size - 1
        else:
            index = int(cursels[0])
            if index == 0:
                index = size - 1
            else:
                index = index - 1

        self.selectitem(index)

    def _selectCmd(self, event=None):

        sels = self.getcurselection()
        if len(sels) == 0:
            item = None
        else:
            item = sels[0]
            self._entryfield.setentry(item)

        cmd = self['selectioncommand']
        if hasattr(cmd, '__call__'):
            if event is None:
                # Return result of selectioncommand for invoke() method.
                return cmd(item)
            else:
                cmd(item)

    #======================================================================

    # Private methods for dropdown combobox.

    def _drawArrow(self, event=None, sunken=0):
        arrow = self._arrowBtn
        if sunken:
            self._arrowRelief = arrow.cget('relief')
            arrow.configure(relief = 'sunken')
        else:
            arrow.configure(relief = self._arrowRelief)

        if self._isPosted and self['fliparrow']:
            direction = 'up'
        else:
            direction = 'down'
        Pmw.drawarrow(arrow, self['entry_foreground'], direction, 'arrow')

    def _postList(self, event = None):
        self._isPosted = 1
        self._drawArrow(sunken=1)

        # Make sure that the arrow is displayed sunken.
        self.update_idletasks()

        x = self._entryfield.winfo_rootx()
        y = self._entryfield.winfo_rooty() + \
            self._entryfield.winfo_height()
        w = self._entryfield.winfo_width() + self._arrowBtn.winfo_width()
        h =  self.__listbox.winfo_height()
        sh = self.winfo_screenheight()

        if y + h > sh and y > sh / 2:
            y = self._entryfield.winfo_rooty() - h

        self._list.configure(hull_width=w)

        Pmw.setgeometryanddeiconify(self._popup, '+%d+%d' % (x, y))

        # Grab the popup, so that all events are delivered to it, and
        # set focus to the listbox, to make keyboard navigation
        # easier.
        Pmw.pushgrab(self._popup, 1, self._unpostList)
        self.__listbox.focus_set()

        self._drawArrow()

        # Ignore the first release of the mouse button after posting the
        # dropdown list, unless the mouse enters the dropdown list.
        self._ignoreRelease = 1

    def _dropdownBtnRelease(self, event):
        if (event.widget == self._list.component('vertscrollbar') or
                event.widget == self._list.component('horizscrollbar')):
            return

        if self._ignoreRelease:
            self._unpostOnNextRelease()
            return

        self._unpostList()

        if (event.x >= 0 and event.x < self.__listbox.winfo_width() and
                event.y >= 0 and event.y < self.__listbox.winfo_height()):
            self._selectCmd()

    def _unpostOnNextRelease(self, event = None):
        self._ignoreRelease = 0

    def _resizeArrow(self, event):
        bw = (int(self._arrowBtn['borderwidth']) +
                int(self._arrowBtn['highlightthickness']))
        newHeight = self._entryfield.winfo_reqheight() - 2 * bw
        newWidth = int(newHeight * self['buttonaspect'])
        self._arrowBtn.configure(width=newWidth, height=newHeight)
        self._drawArrow()

    def _unpostList(self, event=None):
        if not self._isPosted:
            # It is possible to get events on an unposted popup.  For
            # example, by repeatedly pressing the space key to post
            # and unpost the popup.  The <space> event may be
            # delivered to the popup window even though
            # Pmw.popgrab() has set the focus away from the
            # popup window.  (Bug in Tk?)
            return

        # Restore the focus before withdrawing the window, since
        # otherwise the window manager may take the focus away so we
        # can't redirect it.  Also, return the grab to the next active
        # window in the stack, if any.
        Pmw.popgrab(self._popup)
        self._popup.withdraw()

        self._isPosted = 0
        self._drawArrow()

    def _selectUnpost(self, event):
        self._unpostList()
        self._selectCmd()

Pmw.forwardmethods(ComboBox, Pmw.ScrolledListBox, '_list')
Pmw.forwardmethods(ComboBox, Pmw.EntryField, '_entryfield')

######################################################################
### File: PmwComboBoxDialog.py
# Not Based on iwidgets version.

import Pmw

class ComboBoxDialog(Pmw.Dialog):
    # Dialog window with simple combobox.

    # Dialog window displaying a list and entry field and requesting
    # the user to make a selection or enter a value

    def __init__(self, parent = None, **kw):
        # Define the megawidget options.
        
        optiondefs = (
            ('borderx',    10,              INITOPT),
            ('bordery',    10,              INITOPT),
        )
        self.defineoptions(kw, optiondefs)

        # Initialise the base class (after defining the options).
        Pmw.Dialog.__init__(self, parent)

        # Create the components.
        interior = self.interior()

        aliases = (
            ('listbox', 'combobox_listbox'),
            ('scrolledlist', 'combobox_scrolledlist'),
            ('entry', 'combobox_entry'),
            ('label', 'combobox_label'),
        )
        self._combobox = self.createcomponent('combobox',
                aliases, None,
                Pmw.ComboBox, (interior,),
                scrolledlist_dblclickcommand = self.invoke,
                dropdown = 0,
        )
        self._combobox.pack(side='top', expand='true', fill='both',
                padx = self['borderx'], pady = self['bordery'])

        if 'activatecommand' not in kw:
            # Whenever this dialog is activated, set the focus to the
            # ComboBox's listbox widget.
            listbox = self.component('listbox')
            self.configure(activatecommand = listbox.focus_set)

        # Check keywords and initialise options.
        self.initialiseoptions()

    # Need to explicitly forward this to override the stupid
    # (grid_)size method inherited from Tkinter.Toplevel.Grid.
    def size(self):
        return self._combobox.size()

    # Need to explicitly forward this to override the stupid
    # (grid_)bbox method inherited from Tkinter.Toplevel.Grid.
    def bbox(self, index):
        return self._combobox.bbox(index)

Pmw.forwardmethods(ComboBoxDialog, Pmw.ComboBox, '_combobox')

######################################################################
### File: PmwLogicalFont.py
import os
import string

def _font_initialise(root, size=None, fontScheme = None):
    global _fontSize
    if size is not None:
        _fontSize = size

    if fontScheme in ('pmw1', 'pmw2'):
        if os.name == 'posix':
            defaultFont = logicalfont('Helvetica')
            menuFont = logicalfont('Helvetica', weight='bold', slant='italic')
            scaleFont = logicalfont('Helvetica', slant='italic')
            root.option_add('*Font',            defaultFont,  'userDefault')
            root.option_add('*Menu*Font',       menuFont,     'userDefault')
            root.option_add('*Menubutton*Font', menuFont,     'userDefault')
            root.option_add('*Scale.*Font',     scaleFont,    'userDefault')

            if fontScheme == 'pmw1':
                balloonFont = logicalfont('Helvetica', -6, pixel = '12')
            else: # fontScheme == 'pmw2'
                balloonFont = logicalfont('Helvetica', -2)
            root.option_add('*Balloon.*Font', balloonFont, 'userDefault')
        else:
            defaultFont = logicalfont('Helvetica')
            root.option_add('*Font', defaultFont,  'userDefault')
    elif fontScheme == 'default':
        defaultFont = ('Helvetica', '-%d' % (_fontSize,), 'bold')
        entryFont = ('Helvetica', '-%d' % (_fontSize,))
        textFont = ('Courier', '-%d' % (_fontSize,))
        root.option_add('*Font',            defaultFont,  'userDefault')
        root.option_add('*Entry*Font',      entryFont,    'userDefault')
        root.option_add('*Text*Font',       textFont,     'userDefault')

def logicalfont(name='Helvetica', sizeIncr = 0, **kw):
    if name not in _fontInfo:
        raise ValueError('font %s does not exist' % name)

    rtn = []
    for field in _fontFields:
        if field in kw:
            logicalValue = kw[field]
        elif field in _fontInfo[name]:
            logicalValue = _fontInfo[name][field]
        else:
            logicalValue = '*'

        if (field, logicalValue) in _propertyAliases[name]:
            realValue = _propertyAliases[name][(field, logicalValue)]
        elif (field, None) in _propertyAliases[name]:
            realValue = _propertyAliases[name][(field, None)]
        elif (field, logicalValue) in _propertyAliases[None]:
            realValue = _propertyAliases[None][(field, logicalValue)]
        elif (field, None) in _propertyAliases[None]:
            realValue = _propertyAliases[None][(field, None)]
        else:
            realValue = logicalValue

        if field == 'size':
            if realValue == '*':
                realValue = _fontSize
            realValue = str((realValue + sizeIncr) * 10)

        rtn.append(realValue)
    return '-'.join(rtn)
    #return str.join(rtn, '-')

def logicalfontnames():
    return list(_fontInfo.keys())

if os.name == 'nt':
    _fontSize = 16
else:
    _fontSize = 14

_fontFields = (
  'registry', 'foundry', 'family', 'weight', 'slant', 'width', 'style',
  'pixel', 'size', 'xres', 'yres', 'spacing', 'avgwidth', 'charset', 'encoding')

# <_propertyAliases> defines other names for which property values may
# be known by.  This is required because italics in adobe-helvetica
# are specified by 'o', while other fonts use 'i'.

_propertyAliases = {}

_propertyAliases[None] = {
  ('slant', 'italic') : 'i',
  ('slant', 'normal') : 'r',
  ('weight', 'light') : 'normal',
  ('width', 'wide') : 'normal',
  ('width', 'condensed') : 'normal',
}

# <_fontInfo> describes a 'logical' font, giving the default values of
# some of its properties.

_fontInfo = {}

_fontInfo['Helvetica'] = {
  'foundry' : 'adobe',
  'family' : 'helvetica',
  'registry' : '',
  'charset' : 'iso8859',
  'encoding' : '1',
  'spacing' : 'p',
  'slant' : 'normal',
  'width' : 'normal',
  'weight' : 'normal',
}

_propertyAliases['Helvetica'] = {
  ('slant', 'italic') : 'o',
  ('weight', 'normal') : 'medium',
  ('weight', 'light') : 'medium',
}

_fontInfo['Times'] = {
  'foundry' : 'adobe',
  'family' : 'times',
  'registry' : '',
  'charset' : 'iso8859',
  'encoding' : '1',
  'spacing' : 'p',
  'slant' : 'normal',
  'width' : 'normal',
  'weight' : 'normal',
}

_propertyAliases['Times'] = {
  ('weight', 'normal') : 'medium',
  ('weight', 'light') : 'medium',
}

_fontInfo['Fixed'] = {
  'foundry' : 'misc',
  'family' : 'fixed',
  'registry' : '',
  'charset' : 'iso8859',
  'encoding' : '1',
  'spacing' : 'c',
  'slant' : 'normal',
  'width' : 'normal',
  'weight' : 'normal',
}

_propertyAliases['Fixed'] = {
  ('weight', 'normal') : 'medium',
  ('weight', 'light') : 'medium',
  ('style', None) : '',
  ('width', 'condensed') : 'semicondensed',
}

_fontInfo['Courier'] = {
  'foundry' : 'adobe',
  'family' : 'courier',
  'registry' : '',
  'charset' : 'iso8859',
  'encoding' : '1',
  'spacing' : 'm',
  'slant' : 'normal',
  'width' : 'normal',
  'weight' : 'normal',
}

_propertyAliases['Courier'] = {
  ('weight', 'normal') : 'medium',
  ('weight', 'light') : 'medium',
  ('style', None) : '',
}

_fontInfo['Typewriter'] = {
  'foundry' : 'b&h',
  'family' : 'lucidatypewriter',
  'registry' : '',
  'charset' : 'iso8859',
  'encoding' : '1',
  'spacing' : 'm',
  'slant' : 'normal',
  'width' : 'normal',
  'weight' : 'normal',
}

_propertyAliases['Typewriter'] = {
  ('weight', 'normal') : 'medium',
  ('weight', 'light') : 'medium',
}

if os.name == 'nt':
    # For some reason 'fixed' fonts on NT aren't.
    _fontInfo['Fixed'] = _fontInfo['Courier']
    _propertyAliases['Fixed'] = _propertyAliases['Courier']
