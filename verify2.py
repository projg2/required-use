#!/usr/bin/env python

import sys
import unittest

from parser import parse_string
from replace_nary import sort_nary
from solve import immutability_sort, parse_immutables
from to_flat3 import flatten3
from validate_ast import validate_ast_passthrough


class SelfConflictingVerifyError(Exception):
    def __init__(self, conditions, effect, sccond):
        super(SelfConflictingVerifyError, self).__init__(
            "Expression (%s => %s) is self-conflicting (both %s and %s can not be true simultaneously)"
            % (conditions, effect, sccond, sccond.negated()))


def verify_self_conflicting(flats):
    # for every path, check for C having foo and !foo
    for c, e in flats:
        for ci in c:
            if ci.negated() in c:
                raise SelfConflictingVerifyError(c, e, ci)


class ImmutabilityVerifyError(Exception):
    def __init__(self, conditions, effect, expected):
        super(ImmutabilityVerifyError, self).__init__(
            "Expression (%s => %s) can alter immutable flag (expected: %s)"
            % (conditions, effect, expected))


def verify_immutability(flats, immutables):
    # for every path, if C can be true, E must not alter immutables
    for c, e in flats:
        for ci in c:
            # if Ci is in immutables, and it evaluates to false,
            # the rule will never apply; if it is not in immutables,
            # we assume it can apply
            if immutables.get(ci.name, ci.enabled) != ci.enabled:
                break
        else:
            if immutables.get(e.name, e.enabled) != e.enabled:
                raise ImmutabilityVerifyError(c, e, e.enabled)


def split_common_prefix(c1, c2):
    # if two paths have common prefix (using node-wise comparison),
    # split it into a separate list
    pfx = []
    c1 = list(c1)
    c2 = list(c2)
    while c1 and c2 and c1[0] is c2[0]:
        pfx.append(c1.pop(0))
        del c2[0]
    return (pfx, c1, c2)


def conditions_can_coexist(c1, c2):
    # ignore common prefix as it will never conflict (the solver does
    # not backtrace to the top node)
    pfx, c1, c2 = split_common_prefix(c1, c2)
    # C1 and C2 can occur simultaneously unless C2 contains a negation
    # of any member of C1 (the condition is symmetric)
    for ci in c1:
        if ci.negated() in c2:
            return False
    return True


class ConflictVerifyError(Exception):
    def __init__(self, c1, c2, e1):
        super(ConflictVerifyError, self).__init__(
            "Expression (%s => %s) can conflict with (%s => %s)"
            % (c1, e1, c2, e1.negated()))


def verify_conflicts(flats):
    # for every unique pair of paths, conflicts occurs if both:
    # 1. E1 = !E2,
    # 2. C1 can occur simultaneously with C2.
    flats = list(flats)
    for i in range(len(flats)):
        c1, e1 = flats[i]
        for j in range(i+1, len(flats)):
            c2, e2 = flats[j]
            if e1 == e2.negated() and conditions_can_coexist(c1, c2):
                raise ConflictVerifyError(c1, c2, e1)


class BackAlterationVerifyError(Exception):
    def __init__(self, cj, ej, ci, ei):
        super(BackAlterationVerifyError, self).__init__(
            "Expression (%s => %s) may enable the condition of (%s => %s)"
            % (cj, ej, ci, ei))


def verify_back_alteration(flats):
    # for every pair of paths (Pi, Pj) so that i < j,
    # back alteration occurs if both:
    # 1. Ej is in the non-common part of Ci,
    # 2. Ci can occur simultaneously with Cj.
    flats = list(flats)
    for i in range(len(flats)):
        ci, ei = flats[i]
        for j in range(i+1, len(flats)):
            cj, ej = flats[j]
            pfx, cis, cjs = split_common_prefix(ci, cj)
            if ej in cis and conditions_can_coexist(cis, cjs):
                # special case: it's fine to have circular conditions
                # like a? ( b ) b? ( a ) since the latter will only
                # occur if b is already true, so the former will not
                # change anything
                if ei in cjs:
                    continue
                raise BackAlterationVerifyError(cj, ej, ci, ei)


def main(constraint_str, immutable_str=''):
    immutables = parse_immutables(immutable_str)
    ast = sort_nary(validate_ast_passthrough(parse_string(constraint_str)),
            immutability_sort(immutables))
    flats = list(flatten3(ast))

    print('Flat items:')
    for i, v in enumerate(flats):
        print('%02d. %s' % (i+1, v))
    print()

    verify_self_conflicting(flats)
    print('Self-conflicting ok.')
    verify_immutability(flats, immutables)
    print('Immutability ok.')
    verify_conflicts(flats)
    print('Conflicts ok.')
    verify_back_alteration(flats)
    print('Back alteration ok.')


class SelfTests(unittest.TestCase):
    def test_self_conflicting(self):
        verify_self_conflicting(flatten3(parse_string('a? ( a? ( b ) )')))
        self.assertRaises(SelfConflictingVerifyError,
            verify_self_conflicting, flatten3(parse_string('a? ( !a? ( b ) )')))

    def test_basic_immutability(self):
        flats = list(flatten3(parse_string('a? ( b )')))
        verify_immutability(flats, {})
        verify_immutability(flats, parse_immutables('b'))
        self.assertRaises(ImmutabilityVerifyError,
            verify_immutability, flats, parse_immutables('!b'))
        verify_immutability(flats, parse_immutables('!a !b'))

    def test_immutability_any_of(self):
        unsorted = list(flatten3(parse_string('|| ( a b c )')))
        verify_immutability(unsorted, {})
        # this one should fail without sorting
        immutables = parse_immutables('!a')
        self.assertRaises(ImmutabilityVerifyError,
            verify_immutability, unsorted, immutables)
        verify_immutability(flatten3(sort_nary(parse_string('|| ( a b c )'),
            immutability_sort(immutables))), immutables)

    def test_immutability_at_most_one_of(self):
        unsorted = list(flatten3(parse_string('?? ( a b c )')))
        verify_immutability(unsorted, {})
        verify_immutability(unsorted, parse_immutables('a'))
        verify_immutability(unsorted, parse_immutables('!a'))
        verify_immutability(unsorted, parse_immutables('!a b'))
        # multiple values can not be enabled
        self.assertRaises(ImmutabilityVerifyError,
            verify_immutability, unsorted, parse_immutables('a b'))
        # this one should fail without sorting
        immutables = parse_immutables('b')
        self.assertRaises(ImmutabilityVerifyError,
            verify_immutability, unsorted, immutables)
        verify_immutability(flatten3(sort_nary(parse_string('?? ( a b c )'),
            immutability_sort(immutables))), immutables)

    def test_conflicts(self):
        verify_conflicts(flatten3(parse_string('a !b')))
        self.assertRaises(ConflictVerifyError,
            verify_conflicts, flatten3(parse_string('a !a')))
        self.assertRaises(ConflictVerifyError,
            verify_conflicts, flatten3(parse_string('a? ( b ) !b')))
        verify_conflicts(flatten3(parse_string('a? ( b ) !a? ( !b )')))

    def test_back_alteration(self):
        verify_back_alteration(flatten3(parse_string('a? ( b ) b? ( c )')))
        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string('b? ( c ) a? ( b )')))
        verify_back_alteration(flatten3(parse_string('b? ( c ) a? ( !b )')))
        # test common prefix logic
        verify_back_alteration(flatten3(parse_string('a? ( b a a )')))
        # test that common prefix is not overzealous
        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string('a? ( b a ) a? ( a )')))

    def test_back_alteration_circular_case(self):
        verify_back_alteration(flatten3(parse_string('!b? ( a ) a? ( !b )')))
        verify_back_alteration(flatten3(parse_string('a? ( b ) b? ( a )')))
        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string('a? ( !b ) b? ( a )')))

    def test_real_case_back_alteration(self):
        # every one in form of: (broken, fixed)

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                '?? ( gstreamer ffmpeg ) cue? ( gstreamer ) upnp-av? ( gstreamer ) !miner-fs? ( !cue !exif !flac !gif !gsf !iptc !iso !jpeg !mp3 !pdf !playlist !tiff !vorbis !xml !xmp !xps )')))
        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'cue? ( gstreamer ) ?? ( gstreamer ffmpeg ) upnp-av? ( gstreamer ) !miner-fs? ( !cue !exif !flac !gif !gsf !iptc !iso !jpeg !mp3 !pdf !playlist !tiff !vorbis !xml !xmp !xps )')))
        verify_back_alteration(flatten3(parse_string(
            'cue? ( gstreamer ) upnp-av? ( gstreamer ) ?? ( gstreamer ffmpeg ) !miner-fs? ( !cue !exif !flac !gif !gsf !iptc !iso !jpeg !mp3 !pdf !playlist !tiff !vorbis !xml !xmp !xps )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'X? ( || ( python_targets_python2_7 python_targets_python3_4 python_targets_python3_5 ) ) test? ( X )')))
        verify_back_alteration(flatten3(parse_string(
            'test? ( X ) X? ( || ( python_targets_python2_7 python_targets_python3_4 python_targets_python3_5 ) )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                '^^ ( python_single_target_pypy python_single_target_pypy3 python_single_target_python2_7 python_single_target_python3_4 python_single_target_python3_5 python_single_target_python3_6 ) python_single_target_pypy? ( python_targets_pypy ) python_single_target_pypy3? ( python_targets_pypy3 ) python_single_target_python2_7? ( python_targets_python2_7 ) python_single_target_python3_4? ( python_targets_python3_4 ) python_single_target_python3_5? ( python_targets_python3_5 ) python_single_target_python3_6? ( python_targets_python3_6 ) vim? ( ^^ ( python_single_target_python2_7 ) )')))
        verify_back_alteration(flatten3(parse_string(
            'vim? ( ^^ ( python_single_target_python2_7 ) ) ^^ ( python_single_target_pypy python_single_target_pypy3 python_single_target_python2_7 python_single_target_python3_4 python_single_target_python3_5 python_single_target_python3_6 ) python_single_target_pypy? ( python_targets_pypy ) python_single_target_pypy3? ( python_targets_pypy3 ) python_single_target_python2_7? ( python_targets_python2_7 ) python_single_target_python3_4? ( python_targets_python3_4 ) python_single_target_python3_5? ( python_targets_python3_5 ) python_single_target_python3_6? ( python_targets_python3_6 )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                '^^ ( yassl openssl libressl ) minimal? ( !extraengine !embedded ) tcmalloc? ( !jemalloc ) jemalloc? ( !tcmalloc ) static? ( yassl )')))
        verify_back_alteration(flatten3(parse_string(
            'static? ( yassl ) ^^ ( yassl openssl libressl ) minimal? ( !extraengine !embedded ) tcmalloc? ( !jemalloc ) jemalloc? ( !tcmalloc )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'addc? ( python gnutls !system-mitkrb5 ) test? ( python ) addns? ( python ) ads? ( acl gnutls ldap ) gpg? ( addc ) ?? ( system-heimdal system-mitkrb5 ) python_targets_python2_7')))
        verify_back_alteration(flatten3(parse_string(
            'gpg? ( addc ) addc? ( python gnutls !system-mitkrb5 ) test? ( python ) addns? ( python ) ads? ( acl gnutls ldap ) ?? ( system-heimdal system-mitkrb5 ) python_targets_python2_7')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'afs? ( kerberos ) backup? ( sqlite ) calalarm? ( http ) http? ( sqlite ) jmap? ( http xapian ) sphinx? ( mysql )')))
        verify_back_alteration(flatten3(parse_string(
            'afs? ( kerberos ) backup? ( sqlite ) calalarm? ( http ) jmap? ( http xapian ) http? ( sqlite ) sphinx? ( mysql )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'all-modules? ( python xdmf2 boost ) java? ( qt5 ) python? ( python_targets_python2_7 ) tcl? ( rendering ) test? ( python ) tk? ( tcl ) web? ( python ) ^^ ( X aqua offscreen )')))
        verify_back_alteration(flatten3(parse_string(
            'all-modules? ( python xdmf2 boost ) java? ( qt5 ) tk? ( tcl ) tcl? ( rendering ) test? ( python ) web? ( python ) ^^ ( X aqua offscreen ) python? ( python_targets_python2_7 )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'alsa? ( sound ) fusionsound? ( sound ) gles? ( video ) nas? ( sound ) opengl? ( video ) pulseaudio? ( sound ) wayland? ( gles ) xinerama? ( X ) xscreensaver? ( X )')))
        verify_back_alteration(flatten3(parse_string(
            'alsa? ( sound ) fusionsound? ( sound ) wayland? ( gles ) gles? ( video ) nas? ( sound ) opengl? ( video ) pulseaudio? ( sound ) xinerama? ( X ) xscreensaver? ( X )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'annotations? ( privatestorage ) avatars? ( vcard ) birthdayreminder? ( vcard ) bookmarks? ( privatestorage ) captchaforms? ( dataforms ) commands? ( dataforms ) datastreamsmanager? ( dataforms ) filemessagearchive? ( messagearchiver ) filestreamsmanager? ( datastreamsmanager ) filetransfer? ( filestreamsmanager datastreamsmanager ) pepmanager? ( servicediscovery ) registration? ( dataforms ) remotecontrol? ( commands dataforms ) servermessagearchive? ( messagearchiver ) sessionnegotiation? ( dataforms )')))
        verify_back_alteration(flatten3(parse_string(
            'annotations? ( privatestorage ) avatars? ( vcard ) birthdayreminder? ( vcard ) bookmarks? ( privatestorage ) captchaforms? ( dataforms ) remotecontrol? ( commands dataforms ) commands? ( dataforms ) filemessagearchive? ( messagearchiver ) filetransfer? ( filestreamsmanager datastreamsmanager ) filestreamsmanager? ( datastreamsmanager ) datastreamsmanager? ( dataforms ) pepmanager? ( servicediscovery ) registration? ( dataforms ) servermessagearchive? ( messagearchiver ) sessionnegotiation? ( dataforms )')))
        verify_back_alteration(flatten3(parse_string(
            'annotations? ( privatestorage ) avatars? ( vcard ) birthdayreminder? ( vcard ) bookmarks? ( privatestorage ) captchaforms? ( dataforms ) remotecontrol? ( commands ) commands? ( dataforms ) filemessagearchive? ( messagearchiver ) filetransfer? ( filestreamsmanager ) filestreamsmanager? ( datastreamsmanager ) datastreamsmanager? ( dataforms ) pepmanager? ( servicediscovery ) registration? ( dataforms ) servermessagearchive? ( messagearchiver ) sessionnegotiation? ( dataforms )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'asm? ( || ( amd64 arm ) arm? ( experimental ) ) ecdh? ( experimental ) java? ( ecdh ) test_openssl? ( test )')))
        verify_back_alteration(flatten3(parse_string(
            'asm? ( || ( amd64 arm ) arm? ( experimental ) ) java? ( ecdh ) ecdh? ( experimental ) test_openssl? ( test )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'autostart? ( dbus ) cairo? ( X ) gtk2? ( dbus ) gtk3? ( dbus ) introspection? ( dbus ) pango? ( cairo ) qt4? ( X dbus )')))
        verify_back_alteration(flatten3(parse_string(
            'autostart? ( dbus ) gtk2? ( dbus ) gtk3? ( dbus ) introspection? ( dbus ) pango? ( cairo ) cairo? ( X ) qt4? ( X dbus )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'bluetooth? ( dbus ) equalizer? ( dbus ) ofono-headset? ( bluetooth ) native-headset? ( bluetooth ) udev? ( || ( alsa oss ) )')))
        verify_back_alteration(flatten3(parse_string(
            'equalizer? ( dbus ) ofono-headset? ( bluetooth ) native-headset? ( bluetooth ) bluetooth? ( dbus ) udev? ( || ( alsa oss ) )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'btree? ( tokyocabinet ) bzip2? ( btree ) zlib? ( btree )')))
        verify_back_alteration(flatten3(parse_string(
            'bzip2? ( btree ) zlib? ( btree ) btree? ( tokyocabinet )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'cdda? ( mythmusic ) cdr? ( mythmusic cdda ) exif? ( mythgallery ) fftw? ( mythmusic ) mythmusic? ( vorbis ) mythnews? ( mythbrowser ) raw? ( mythgallery ) mythnetvision? ( python_targets_python2_7 )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'cdda? ( udev ) google? ( gnome-online-accounts ) mtp? ( udev ) udisks? ( udev ) systemd? ( udisks )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'cdda? ( udisks || ( cddb musicbrainz ) ) cddb? ( cdda taglib ) mtp? ( taglib udisks ) musicbrainz? ( cdda taglib ) replaygain? ( taglib )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'cgi? ( !minimal ) apache? ( cgi )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'cgi? ( perl ) cvs? ( perl ) mediawiki? ( perl ) mediawiki-experimental? ( mediawiki ) subversion? ( perl ) webdav? ( curl ) python? ( python_targets_python2_7 )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'charmap? ( python ) git? ( python ) python? ( ^^ ( python_single_target_python3_4 python_single_target_python3_5 ) python_single_target_python3_4? ( python_targets_python3_4 ) python_single_target_python3_5? ( python_targets_python3_5 ) ) terminal? ( python ) zeitgeist? ( python )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'cli? ( ^^ ( readline libedit ) ) truetype? ( gd ) vpx? ( gd ) cjk? ( gd ) exif? ( gd ) xpm? ( gd ) gd? ( zlib ) simplexml? ( xml ) soap? ( xml ) wddx? ( xml ) xmlrpc? ( || ( xml iconv ) ) xmlreader? ( xml ) xslt? ( xml ) ldap-sasl? ( ldap ) mhash? ( hash ) phar? ( hash ) libmysqlclient? ( || ( mysql mysqli pdo ) ) qdbm? ( !gdbm ) readline? ( !libedit ) recode? ( !imap !mysql !mysqli ) sharedmem? ( !threads ) !cli? ( !cgi? ( !fpm? ( !apache2? ( !embed? ( cli ) ) ) ) )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'cli? ( ^^ ( readline libedit ) ) truetype? ( gd ) webp? ( gd ) cjk? ( gd ) exif? ( gd ) xpm? ( gd ) gd? ( zlib ) simplexml? ( xml ) soap? ( xml ) wddx? ( xml ) xmlrpc? ( || ( xml iconv ) ) xmlreader? ( xml ) xslt? ( xml ) ldap-sasl? ( ldap ) mhash? ( hash ) phar? ( hash ) qdbm? ( !gdbm ) readline? ( !libedit ) recode? ( !imap !mysqli ) sharedmem? ( !threads ) mysql? ( || ( mysqli pdo ) ) || ( cli cgi fpm apache2 embed phpdbg )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'corefonts? ( truetype ) test? ( corefonts )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'cpu_flags_x86_popcnt? ( cpu_flags_x86_sse3 ) cpu_flags_x86_sse4a? ( cpu_flags_x86_popcnt cpu_flags_x86_sse3 ) cpu_flags_x86_sse4_2? ( cpu_flags_x86_popcnt cpu_flags_x86_sse4_1 ) cpu_flags_x86_sse4_1? ( cpu_flags_x86_ssse3 ) cpu_flags_x86_ssse3? ( cpu_flags_x86_sse3 ) cpu_flags_x86_sse3? ( cpu_flags_x86_sse2 ) python? ( || ( python_targets_python2_7 python_targets_python3_4 python_targets_python3_5 python_targets_python3_6 ) )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'cpu_flags_x86_sse2? ( cpu_flags_x86_mmx ) cpu_flags_x86_ssse3? ( cpu_flags_x86_sse2 ) test? ( threads )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'cpu_flags_x86_sse? ( cpu_flags_x86_mmx ) cpu_flags_x86_sse2? ( cpu_flags_x86_mmx cpu_flags_x86_sse ) cpu_flags_x86_3dnow? ( cpu_flags_x86_mmx ) nuv? ( lzo )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'cuda? ( tesseract? ( opencl ) ) gflags? ( contrib ) glog? ( contrib ) contrib_cvv? ( contrib qt5 ) contrib_hdf? ( contrib ) contrib_sfm? ( contrib eigen gflags glog ) opengl? ( || ( gtk qt5 ) ) python? ( || ( python_targets_python2_7 python_targets_python3_4 python_targets_python3_5 ) ) tesseract? ( contrib )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'd3d9? ( dri3 gallium ) llvm? ( gallium ) opencl? ( gallium llvm ) openmax? ( gallium ) gles1? ( egl ) gles2? ( egl ) vaapi? ( gallium ) vdpau? ( gallium ) vulkan? ( || ( video_cards_i965 video_cards_radeonsi ) video_cards_radeonsi? ( llvm ) ) wayland? ( egl gbm ) xa? ( gallium ) video_cards_freedreno? ( gallium ) video_cards_intel? ( classic ) video_cards_i915? ( || ( classic gallium ) ) video_cards_i965? ( classic ) video_cards_imx? ( gallium ) video_cards_nouveau? ( || ( classic gallium ) ) video_cards_radeon? ( || ( classic gallium ) gallium? ( x86? ( llvm ) amd64? ( llvm ) ) ) video_cards_r100? ( classic ) video_cards_r200? ( classic ) video_cards_r300? ( gallium x86? ( llvm ) amd64? ( llvm ) ) video_cards_r600? ( gallium ) video_cards_radeonsi? ( gallium llvm ) video_cards_vivante? ( gallium gbm ) video_cards_vmware? ( gallium )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'dbus? ( python_targets_python2_7 ) networkmanager? ( dbus ) python? ( python_targets_python2_7 )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'dga? ( X ) dvdnav? ( dvd ) enca? ( iconv ) ggi? ( X ) libass? ( truetype ) opengl? ( X ) osdmenu? ( X ) truetype? ( iconv ) vdpau? ( X ) vidix? ( X ) xinerama? ( X ) xscreensaver? ( X ) xv? ( X ) xvmc? ( xv )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'doc? ( hdf5 fftw ) python? ( hdf5 || ( python_targets_python2_7 ) ) test? ( hdf5 python fftw )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'doc? ( || ( python_targets_python2_7 ) ) excel? ( || ( python_targets_python2_7 ) ) fltk? ( || ( python_targets_python2_7 ) ) gtk2? ( || ( python_targets_python2_7 ) ) wxwidgets? ( || ( python_targets_python2_7 ) ) test? ( cairo fltk latex pyside qt5 qt4 tk wxwidgets || ( gtk2 gtk3 ) ) || ( python_targets_python2_7 python_targets_python3_4 python_targets_python3_5 python_targets_python3_6 )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'dump? ( agg ffmpeg ) fbcon? ( agg ) nsplugin? ( gtk ) openvg? ( egl ) python? ( gtk ) vaapi? ( agg ffmpeg ) || ( agg cairo opengl openvg ) || ( dump fbcon gtk sdl )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'firewalld? ( server ) gdbm? ( server ) iptables? ( server ) nfqueue? ( server ) python? ( || ( python_targets_python2_7 ) ) server? ( ^^ ( firewalld iptables ) ) udp-server? ( server )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'firewalld? ( virt-network ) libvirtd? ( || ( lxc openvz qemu uml virtualbox xen ) ) lxc? ( caps libvirtd ) openvz? ( libvirtd ) policykit? ( dbus ) qemu? ( libvirtd ) uml? ( libvirtd ) vepa? ( macvtap ) virt-network? ( libvirtd ) virtualbox? ( libvirtd ) xen? ( libvirtd )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'geoloc? ( introspection ) gles2? ( egl ) introspection? ( gstreamer ) webgl? ( ^^ ( gles2 opengl ) ) !webgl? ( ?? ( gles2 opengl ) ) || ( aqua X )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'geolocation? ( introspection ) gles2? ( egl ) introspection? ( gstreamer ) nsplugin? ( X ) webgl? ( ^^ ( gles2 opengl ) ) !webgl? ( ?? ( gles2 opengl ) ) webgl? ( gstreamer ) wayland? ( egl ) || ( aqua wayland X )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'geolocation? ( introspection ) gles2? ( egl ) introspection? ( gstreamer ) webgl? ( ^^ ( gles2 opengl ) ) !webgl? ( ?? ( gles2 opengl ) ) || ( aqua wayland X )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'gpu-accel? ( gtk3 ) map? ( gpu-accel )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'gtk? ( X ) || ( gtk qt4 qt5 )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'gtk? ( X ) || ( gtk qt4 qt5 ) plasma? ( qt5 )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'hcache? ( ^^ ( berkdb gdbm lmdb qdbm tokyocabinet ) ) imap? ( ssl ) pop? ( ssl ) nntp? ( ssl ) smime? ( ssl !gnutls ) smtp? ( ssl ) sasl? ( || ( imap pop smtp nntp ) ) kerberos? ( || ( imap pop smtp nntp ) )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'iapbs? ( fetk ) mpi? ( !python ) python? ( tools fetk iapbs python_targets_python2_7 ) python_targets_python2_7')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'java? ( sdk ) python? ( sdk ) vboxwebsrv? ( java ) python_targets_python2_7')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'mpi? ( hdf5 ) openmp? ( !threads ) png? ( zlib ) pdf? ( png ) python? ( python_targets_python2_7 )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'nmbug? ( python ) python? ( || ( python_targets_python2_7 python_targets_python3_4 python_targets_python3_5 python_targets_python3_6 ) ) test? ( crypt emacs python valgrind )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'postgres? ( dlz ) berkdb? ( dlz ) mysql? ( dlz !threads ) odbc? ( dlz ) ldap? ( dlz ) gost? ( !libressl ssl ) threads? ( caps ) dnstap? ( threads ) python? ( || ( python_targets_python2_7 python_targets_python3_4 python_targets_python3_5 python_targets_python3_6 ) )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'pulseaudio? ( sound ) opengl? ( || ( X sdl wayland ) ) gles? ( || ( X wayland ) ) gles? ( !sdl ) gles? ( egl ) sdl? ( opengl ) wayland? ( egl !opengl gles ) xim? ( X )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'python? ( ^^ ( python_single_target_python2_7 python_single_target_python3_4 python_single_target_python3_5 ) python_single_target_python2_7? ( python_targets_python2_7 ) python_single_target_python3_4? ( python_targets_python3_4 ) python_single_target_python3_5? ( python_targets_python3_5 ) ) test? ( python )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'python? ( introspection || ( python_targets_python2_7 python_targets_python3_4 python_targets_python3_5 ) ) test? ( python )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'python? ( python_targets_python2_7 ) test? ( python )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'python_targets_python2_7 analog? ( filter ) digital? ( filter analog ) pager? ( filter analog ) qt4? ( filter ) uhd? ( filter analog ) fcd? ( || ( alsa oss ) ) wavelet? ( analog ) wxwidgets? ( filter analog )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'python_targets_python2_7 audio? ( || ( alsa oss jack portaudio ) ) alsa? ( audio ) oss? ( audio ) jack? ( audio ) portaudio? ( audio ) analog? ( filter ) digital? ( filter analog ) dtv? ( fec ) pager? ( filter analog ) qt4? ( filter ) uhd? ( filter analog ) fcd? ( || ( alsa oss ) ) wavelet? ( analog ) wxwidgets? ( filter analog )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'python_targets_python2_7 server? ( client ) test? ( server )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'python_targets_python3_5 player? ( game-engine !headless ) cuda? ( cycles ) cycles? ( boost openexr tiff openimageio ) colorio? ( boost ) openvdb? ( boost ) opensubdiv? ( cuda ) nls? ( boost ) openal? ( boost ) game-engine? ( boost ) ?? ( ffmpeg libav )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'ruby? ( ^^ ( ruby_targets_ruby21 ruby_targets_ruby22 ) ) ruby_targets_ruby21? ( ruby ) ruby_targets_ruby22? ( ruby )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'server? ( tokudb? ( jemalloc ) ) static? ( !pam ) jdbc? ( extraengine server !static ) ^^ ( yassl openssl libressl ) !server? ( !extraengine !embedded ) ?? ( tcmalloc jemalloc ) static? ( !libressl !openssl yassl )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'sqs? ( python_targets_python2_7 ) doc? ( python_targets_python2_7 amqplib sqs ) || ( python_targets_pypy python_targets_python2_7 python_targets_python3_4 python_targets_python3_5 )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'tokudb? ( jemalloc ) tokudb-backup-plugin? ( tokudb ) ^^ ( yassl openssl libressl ) !server? ( !extraengine !embedded ) ?? ( tcmalloc jemalloc ) static? ( !libressl !openssl yassl )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'tools? ( X ) static-libs? ( tools )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                '|| ( X server monolithic ) ayatana? ( || ( X monolithic ) ) crypt? ( || ( server monolithic ) ) dbus? ( || ( X monolithic ) ) kde? ( || ( X monolithic ) phonon ) phonon? ( || ( X monolithic ) ) postgres? ( || ( server monolithic ) ) qt5? ( !ayatana ) snorenotify? ( qt5 || ( X monolithic ) ) syslog? ( || ( server monolithic ) ) webkit? ( qt5 || ( X monolithic ) )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                '|| ( agent frontend proxy server ) proxy? ( ^^ ( mysql oracle postgres sqlite odbc ) ) server? ( ^^ ( mysql oracle postgres sqlite odbc ) ) static? ( !oracle !snmp )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                '|| ( calligra_features_author calligra_features_braindump calligra_features_flow calligra_features_gemini calligra_features_karbon calligra_features_kexi calligra_features_krita calligra_features_plan calligra_features_sheets calligra_features_stage calligra_features_words ) calligra_features_author? ( calligra_features_words ) calligra_features_gemini? ( opengl ) calligra_features_krita? ( eigen exif lcms opengl ) calligra_features_plan? ( pim ) calligra_features_sheets? ( eigen ) calligra_features_stage? ( webkit ) vc? ( calligra_features_krita ) test? ( calligra_features_karbon )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                '|| ( cgi mono perl go lua php pypy python python_asyncio python_gevent ruby ) uwsgi_plugins_logcrypto? ( ssl ) uwsgi_plugins_sslrouter? ( ssl ) routing? ( pcre ) uwsgi_plugins_emperor_zeromq? ( zeromq ) uwsgi_plugins_forkptyrouter? ( uwsgi_plugins_corerouter ) uwsgi_plugins_router_xmldir? ( xml ) pypy? ( python_targets_python2_7 ) python? ( || ( python_targets_pypy python_targets_python2_7 python_targets_python3_4 python_targets_python3_5 ) ) python_asyncio? ( python_targets_python3_4 python_gevent ) python_gevent? ( python ) expat? ( xml ) php? ( || ( php_targets_php5-6 php_targets_php7-0 ) )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                '|| ( cli gui ) gui? ( ^^ ( qt4 qt5 ) ) cli? ( ^^ ( qt4 qt5 ) ) feedreader? ( gui ) voip? ( gui )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                '|| ( cli libmpv ) aqua? ( opengl ) egl? ( || ( gbm X wayland ) ) enca? ( iconv ) gbm? ( drm egl ) lcms? ( || ( opengl egl ) ) libguess? ( iconv ) luajit? ( lua ) test? ( || ( opengl egl ) ) uchardet? ( iconv ) v4l? ( || ( alsa oss ) ) vaapi? ( || ( gbm X wayland ) ) vdpau? ( X ) wayland? ( egl ) xinerama? ( X ) xscreensaver? ( X ) xv? ( X ) zsh-completion? ( cli )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                '|| ( crypt pam ) pam? ( !xlockrc ) xlockrc? ( !pam )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                '|| ( gcrypt libressl nettle openssl ) d3d9? ( dri3 gallium ) llvm? ( gallium ) opencl? ( gallium llvm ) openmax? ( gallium ) gles1? ( egl ) gles2? ( egl ) vaapi? ( gallium ) vdpau? ( gallium ) vulkan? ( video_cards_i965 ) wayland? ( egl gbm ) xa? ( gallium ) video_cards_freedreno? ( gallium ) video_cards_intel? ( classic ) video_cards_i915? ( || ( classic gallium ) ) video_cards_i965? ( classic ) video_cards_nouveau? ( || ( classic gallium ) ) video_cards_radeon? ( || ( classic gallium ) gallium? ( x86? ( llvm ) amd64? ( llvm ) ) ) video_cards_r100? ( classic ) video_cards_r200? ( classic ) video_cards_r300? ( gallium x86? ( llvm ) amd64? ( llvm ) ) video_cards_r600? ( gallium ) video_cards_radeonsi? ( gallium llvm ) video_cards_vmware? ( gallium )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                '|| ( keccak scrypt sha256d ) || ( antminer avalon avalonmm bfsb bfx bifury bigpic bitforce bitfury cointerra cpumining drillbit dualminer gridseed hashbuster hashbuster2 hashfast icarus klondike littlefury metabank modminer nanofury opencl proxy twinfury x6500 zeusminer ztex ) adl? ( opencl ) antminer? ( sha256d ) avalon? ( sha256d ) avalonmm? ( sha256d ) bfsb? ( sha256d bitfury ) bfx? ( sha256d bitfury libusb ) bifury? ( sha256d ) bigpic? ( sha256d bitfury ) bitforce? ( sha256d ) bitfury? ( sha256d ) cointerra? ( sha256d ) drillbit? ( sha256d bitfury ) dualminer? ( || ( sha256d scrypt ) icarus ) gridseed? ( scrypt ) hashbuster? ( sha256d bitfury ) hashbuster2? ( sha256d bitfury libusb ) hashfast? ( sha256d ) icarus? ( || ( scrypt sha256d ) ) jingtian? ( sha256d ) keccak? ( || ( cpumining opencl proxy ) ) klondike? ( sha256d libusb ) littlefury? ( sha256d bitfury ) lm_sensors? ( opencl ) metabank? ( sha256d bitfury ) minion? ( sha256d ) modminer? ( sha256d ) nanofury? ( sha256d bitfury ) scrypt? ( || ( cpumining dualminer gridseed opencl proxy zeusminer ) ) sha256d? ( || ( antminer avalon avalonmm bfx bifury bitforce bfsb bigpic bitfury cointerra cpumining drillbit dualminer hashbuster hashbuster2 hashfast icarus jingtian klondike littlefury metabank modminer nanofury opencl proxy rockminer twinfury x6500 ztex ) ) twinfury? ( bitfury ) unicode? ( ncurses ) proxy? ( || ( proxy_getwork proxy_stratum ) ) proxy_getwork? ( proxy ) proxy_stratum? ( proxy ) rockminer? ( sha256d ) twinfury? ( sha256d ) x6500? ( sha256d libusb ) zeusminer? ( scrypt icarus ) ztex? ( sha256d libusb )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                '|| ( oss alsa portaudio coreaudio pulseaudio ) video? ( || ( opengl sdl X ) ) theora? ( video ) X? ( video ) v4l? ( video ) opengl? ( video )')))

        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                '|| ( python_targets_python2_7 python_targets_python3_4 python_targets_python3_5 python_targets_python3_6 ) bluetooth? ( gui ) declarative? ( gui network ) designer? ( widgets ) help? ( gui widgets ) location? ( positioning ) multimedia? ( gui network ) opengl? ( gui widgets ) positioning? ( gui ) printsupport? ( gui widgets ) sensors? ( gui ) serialport? ( gui ) sql? ( widgets ) svg? ( gui widgets ) testlib? ( gui widgets ) webchannel? ( network ) webengine? ( network widgets? ( webchannel ) ) webkit? ( gui network printsupport widgets ) websockets? ( network ) widgets? ( gui ) xmlpatterns? ( network )')))

    def test_real_case_back_alteration_false_positives(self):
        # those are potential false positives
        # all of them can be solved within a single iteration

        # P3 duplicates P1
        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                '!jit? ( !shadowstack ) x86? ( !cpu_flags_x86_sse2? ( !jit !shadowstack ) )')))
        verify_back_alteration(flatten3(parse_string(
            'x86? ( !cpu_flags_x86_sse2? ( !jit !shadowstack ) ) !jit? ( !shadowstack )')))
        verify_back_alteration(flatten3(parse_string(
            'x86? ( !cpu_flags_x86_sse2? ( !jit ) ) !jit? ( !shadowstack )')))

        # Pn is equivalent to P1
        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                '^^ ( yassl openssl libressl ) !server? ( !extraengine !embedded ) ?? ( tcmalloc jemalloc ) static? ( !libressl !openssl yassl )')))
        verify_back_alteration(flatten3(parse_string(
            'static? ( !libressl !openssl yassl ) ^^ ( yassl openssl libressl ) !server? ( !extraengine !embedded ) ?? ( tcmalloc jemalloc )')))
        verify_back_alteration(flatten3(parse_string(
            'static? ( yassl ) ^^ ( yassl openssl libressl ) !server? ( !extraengine !embedded ) ?? ( tcmalloc jemalloc )')))

        # skins forces X, and so do qt*
        self.assertRaises(BackAlterationVerifyError,
            verify_back_alteration, flatten3(parse_string(
                'aalib? ( X ) bidi? ( truetype ) cddb? ( cdda ) dvb? ( dvbpsi ) dxva2? ( avcodec ) ffmpeg? ( avcodec avformat swscale ) fontconfig? ( truetype ) gnutls? ( gcrypt ) httpd? ( lua ) libcaca? ( X ) libtar? ( skins ) libtiger? ( kate ) qt4? ( X ) qt5? ( X ) sdl? ( X ) skins? ( truetype X xml || ( qt4 qt5 ) ) vaapi? ( avcodec X ) vdpau? ( X ) vlm? ( encode ) xv? ( xcb )')))
        verify_back_alteration(flatten3(parse_string(
            'aalib? ( X ) bidi? ( truetype ) cddb? ( cdda ) dvb? ( dvbpsi ) dxva2? ( avcodec ) ffmpeg? ( avcodec avformat swscale ) fontconfig? ( truetype ) gnutls? ( gcrypt ) httpd? ( lua ) libcaca? ( X ) libtar? ( skins ) libtiger? ( kate ) sdl? ( X ) skins? ( truetype X xml || ( qt4 qt5 ) ) qt4? ( X ) qt5? ( X ) vaapi? ( avcodec X ) vdpau? ( X ) vlm? ( encode ) xv? ( xcb )')))


    def test_real_case_conflicts(self):
        self.assertRaises(ConflictVerifyError,
            verify_conflicts, flatten3(parse_string(
                '^^ ( gcrypt kernel nettle openssl ) python? ( || ( python_targets_python2_7 python_targets_python3_4 python_targets_python3_5 python_targets_python3_6 ) ) static? ( !gcrypt )')))

        self.assertRaises(ConflictVerifyError,
            verify_conflicts, flatten3(parse_string(
                '^^ ( openssl nss gnutls ) nettle? ( gnutls )')))

        self.assertRaises(ConflictVerifyError,
            verify_conflicts, flatten3(parse_string(
                'dane? ( !gnutls ) dmarc? ( spf dkim ) pkcs11? ( gnutls ) spf? ( exiscan-acl ) srs? ( exiscan-acl )')))

        self.assertRaises(ConflictVerifyError,
            verify_conflicts, flatten3(parse_string(
                'debug? ( !binary ) !amd64? ( !x86? ( binary ) )')))

        self.assertRaises(ConflictVerifyError,
            verify_conflicts, flatten3(parse_string(
                'device-mapper-only? ( !clvm !cman !lvm1 !lvm2create_initrd !thin ) systemd? ( udev ) static? ( !udev )')))

        self.assertRaises(ConflictVerifyError,
            verify_conflicts, flatten3(parse_string(
                'emacs? ( gtk ) !curl? ( !gtk )')))

        self.assertRaises(ConflictVerifyError,
            verify_conflicts, flatten3(parse_string(
                'fasteap? ( !gnutls !ssl ) smartcard? ( ssl ) ?? ( qt4 qt5 )')))

        self.assertRaises(ConflictVerifyError,
            verify_conflicts, flatten3(parse_string(
                'fasteap? ( !ssl ) smartcard? ( ssl )')))

        self.assertRaises(ConflictVerifyError,
            verify_conflicts, flatten3(parse_string(
                'minimal? ( !oqgraph ) minimal? ( !sphinx ) tokudb? ( jemalloc ) tcmalloc? ( !jemalloc ) jemalloc? ( !tcmalloc ) minimal? ( !cluster !extraengine !embedded ) static? ( !ssl )')))

        self.assertRaises(ConflictVerifyError,
            verify_conflicts, flatten3(parse_string(
                'static? ( !plugins !pkcs11 ) lzo? ( !lz4 ) pkcs11? ( ssl ) mbedtls? ( ssl !libressl ) pkcs11? ( ssl ) !plugins? ( !pam !down-root ) inotify? ( plugins )')))

        self.assertRaises(ConflictVerifyError,
            verify_conflicts, flatten3(parse_string(
                'systemd? ( !python_single_target_pypy ) ^^ ( python_single_target_pypy python_single_target_python2_7 python_single_target_python3_4 python_single_target_python3_5 ) python_single_target_pypy? ( python_targets_pypy ) python_single_target_python2_7? ( python_targets_python2_7 ) python_single_target_python3_4? ( python_targets_python3_4 ) python_single_target_python3_5? ( python_targets_python3_5 )')))

        self.assertRaises(ConflictVerifyError,
            verify_conflicts, flatten3(parse_string(
                'test? ( gflags ) sparse? ( lapack ) abi_x86_32? ( !sparse !lapack )')))

        self.assertRaises(ConflictVerifyError,
            verify_conflicts, flatten3(parse_string(
                'threads? ( !cxx !mpi !fortran !hl ) fortran2003? ( fortran )')))

        self.assertRaises(ConflictVerifyError,
            verify_conflicts, flatten3(parse_string(
                '|| ( mysql sqlite ) taglib? ( !id3tag ) id3tag? ( !taglib ) thumbnail? ( ffmpeg !libextractor ) ffmpeg? ( !libextractor ) libextractor? ( !ffmpeg !thumbnail )')))

        self.assertRaises(ConflictVerifyError,
            verify_conflicts, flatten3(parse_string(
                '|| ( python_targets_python2_7 ) gtk2? ( gtk ) qemu_softmmu_targets_arm? ( fdt ) qemu_softmmu_targets_microblaze? ( fdt ) qemu_softmmu_targets_mips64el? ( fdt ) qemu_softmmu_targets_ppc? ( fdt ) qemu_softmmu_targets_ppc64? ( fdt ) sdl2? ( sdl ) static? ( static-user !alsa !bluetooth !gtk !gtk2 !opengl !pulseaudio ) virtfs? ( xattr ) vte? ( gtk )')))


if __name__ == '__main__':
    main(*sys.argv[1:])
