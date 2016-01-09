# -*- coding: utf-8 -*-

from docutils import nodes
from docutils.parsers.rst import Directive, directives
from sphinx import addnodes
from sphinx.domains import std, ObjType
from sphinx.util.docfields import Field, TypedField
from sphinx.roles import XRefRole

def setup(app):
    std.StandardDomain.object_types['ghc-flag'] = ObjType('ghc-flag', 'ghc-flag')
    app.add_role_to_domain('std', 'ghc-flag', XRefRole())
    app.add_directive_to_domain('std', 'ghc-flag', GhcFlagDirective)

    std.StandardDomain.object_types['rts-flag'] = ObjType('rts-flag', 'rts-flag')
    app.add_role_to_domain('std', 'rts-flag', XRefRole())
    app.add_directive_to_domain('std', 'rts-flag', RtsFlagDirective)

    app.add_node(FlagList)
    app.add_directive('flag-list', FlagListDirective)
    app.connect('doctree-resolved', process_flag_lists)
    return {'version': 0.1}

class FlagList(nodes.General, nodes.Element):
    def __init__(self, flag_type, category):
        self.flag_type = flag_type
        self.category = category
        nodes.Element.__init__(self, '')

class FlagListDirective(Directive):
    has_content = False
    required_arguments = 0
    optional_arguments = 0
    option_spec = {
        'flag_type': str,   # either "ghc-flag" or "rts-flag"
        'category': str,
    }

    def run(self):
        flag_type = self.options['flag_type']
        category = self.options['category']
        env = self.state.document.settings.env
        return [FlagList(flag_type, category)]

def process_flag_lists(app, doctree, fromdocname):
    print 'process flag lists'
    env = app.builder.env
    for node in doctree.traverse(FlagList):
        category = node.category
        all_flags = env.domains['std'].data['ghc-'+node.flag_type]
        print all_flags
        flags = [summary
                 for (flag, (cat, targetname, summary)) in all_flags.items()
                 if cat == category ]
        content = []
        node.replace_self(flags)

class FlagDirective(std.GenericObject):
    option_spec = {
        'static': directives.flag,
        'noindex': directives.flag,
    }

    doc_field_types = [
        Field('since', label='Introduced in GHC version', names=['since']),
        Field('default', label='Default value', names=['default']),
    ]

    def parse_node(self, env, sig, signode):
        import re
        names = []
        for i, flag in enumerate(sig.split(',')):
            flag = flag.strip()
            equals = '='
            parts = flag.split('=')
            if len(parts) == 1:
                equals=''
                parts = flag.split()
            if len(parts) == 0: continue

            name = parts[0]
            names.append(name)
            sig = equals + ' '.join(parts[1:])
            sig = re.sub(ur'<([-a-zA-Z ]+)>', ur'⟨\1⟩', sig)
            if i > 0:
                signode += addnodes.desc_name(', ', ', ')
            signode += addnodes.desc_name(name, name)
            if len(sig) > 0:
                signode += addnodes.desc_addname(sig, sig)

        return names[0]

    def after_content(self):
        """ Add flag to flag list """
        if 'summary' in self.options:
            summary = self.options.summary
        else:
            node = nodes.description()
            self.state.nested_parse(self.content, self.content_offset, node)
            summary = node

        targetname = '%s-%s' % (self.objtype, self.names[0])
        flags = self.env.domaindata['std'].setdefault('ghc-'+self.objtype, {})
        for name in self.names:
            flags[name] = ('GC', targetname, summary)

class RtsFlagDirective(FlagDirective):
    indextemplate = 'pair: %s; RTS option'

class GhcFlagDirective(FlagDirective):
    doc_field_types = Flag.doc_field_types + [
        Field('static'),
    ]
    indextemplate = 'pair: %s; GHC option'
