/*
 * Copyright (c) 1999-2016 Apple Inc. All rights reserved.
 *
 * @APPLE_LICENSE_HEADER_START@
 *
 * This file contains Original Code and/or Modifications of Original Code
 * as defined in and that are subject to the Apple Public Source License
 * Version 2.0 (the 'License'). You may not use this file except in
 * compliance with the License. Please obtain a copy of the License at
 * http://www.opensource.apple.com/apsl/ and read it before using this
 * file.
 *
 * The Original Code and all software distributed under the License are
 * distributed on an 'AS IS' basis, WITHOUT WARRANTY OF ANY KIND, EITHER
 * EXPRESS OR IMPLIED, AND APPLE HEREBY DISCLAIMS ALL SUCH WARRANTIES,
 * INCLUDING WITHOUT LIMITATION, ANY WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE, QUIET ENJOYMENT OR NON-INFRINGEMENT.
 * Please see the License for the specific language governing rights and
 * limitations under the License.
 *
 * @APPLE_LICENSE_HEADER_END@
 */
/*-
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * Copyright (c) 1990, 1993, 1994
 *	The Regents of the University of California.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#if 0
#ifndef lint
static const char sccsid[] = "@(#)table.c	8.3 (Berkeley) 4/2/94";
#endif /* not lint */
#endif
#include <sys/cdefs.h>
__FBSDID("$FreeBSD$");

#include <sys/types.h>
#include <stddef.h>
#include "chpass.h"

#ifdef __APPLE__
#include "open_directory.h"
#endif /* __APPLE__ */

ENTRY list[] = {
#ifdef __APPLE__
	{ "Login",						display_string,	p_login,	1,   5, ": ",	&kODAttributeTypeRecordName, },
	{ "Password",					display_string,	p_passwd,	1,   8, ": ",	&kODAttributeTypePassword, },
	{ "Uid [#]",					display_string,	p_uid,		1,   3, ": ",	&kODAttributeTypeUniqueID, },
	{ "Gid [# or name]",			display_string,	p_gid,		1,   3, ": ",	&kODAttributeTypePrimaryGroupID, },
	{ "Generated uid",				display_string,	p_uuid,		1,	13,	NULL,	&kODAttributeTypeGUID, },
	{ "Home directory",				display_string,	p_hdir,		1,  14, ": ",	&kODAttributeTypeNFSHomeDirectory, },
	{ "Shell",						display_string,	p_shell,	1,   5, ": ",	&kODAttributeTypeUserShell, },
	{ "Full Name",					display_string,	p_gecos,	1,   9, ":,",	&kODAttributeTypeFullName, },
	{ "Office Location",			display_string,	p_gecos,	1,   8, ":,",	&kODAttributeTypeBuilding, },
	{ "Office Phone",				display_string,	p_gecos,	1,  12, ":,",	&kODAttributeTypePhoneNumber,	},
	{ "Home Phone",					display_string,	p_gecos,	1,  10, ":,",	&kODAttributeTypeHomePhoneNumber,	},
	{ NULL,							NULL,			NULL,		0,	0,	NULL,	NULL,},
#else /* !__APPLE__ */
	{ "login",		p_login,  1,   5, ": ", NULL },
	{ "password",		p_passwd, 1,   8, ": ", NULL },
	{ "uid",		p_uid,    1,   3, ": ", NULL },
	{ "gid",		p_gid,    1,   3, ": ", NULL },
	{ "class",		p_class,  1,   5, ": ", NULL },
	{ "change",		p_change, 1,   6, NULL, NULL },
	{ "expire",		p_expire, 1,   6, NULL, NULL },
#ifdef RESTRICT_FULLNAME_CHANGE		/* do not allow fullname changes */
	{ "full name",		p_gecos,  1,   9, ":,", NULL },
#else
	{ "full name",		p_gecos,  0,   9, ":,", NULL },
#endif
	{ "office phone",	p_gecos,  0,  12, ":,", NULL },
	{ "home phone",		p_gecos,  0,  10, ":,", NULL },
	{ "office location",	p_gecos,  0,  15, ":,", NULL },
	{ "other information",	p_gecos,  0,  11, ": ", NULL },
	{ "home directory",	p_hdir,   1,  14, ": ", NULL },
	{ "shell",		p_shell,  0,   5, ": ", NULL },
	{ NULL, NULL, 0, 0, NULL, NULL },
#endif /* __APPLE__ */
};
