/*
 * Copyright (c) 1999, 2000-2001 Apple Computer, Inc. All rights reserved.
 *
 * @APPLE_LICENSE_HEADER_START@
 * 
 * Copyright (c) 1999-2003 Apple Computer, Inc.  All Rights Reserved.
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
 * Copyright (c) 1988, 1993
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
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *	This product includes software developed by the University of
 *	California, Berkeley and its contributors.
 * 4. Neither the name of the University nor the names of its contributors
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

#ifndef lint
static const char copyright[] =
"@(#) Copyright (c) 1988, 1993\n\
	The Regents of the University of California.  All rights reserved.\n";
#endif /* not lint */

#ifndef lint
#if 0
static char sccsid[] = "@(#)kdump.c	8.1 (Berkeley) 6/6/93";
#endif
static const char rcsid[] =
  "$FreeBSD: src/usr.bin/kdump/kdump.c,v 1.17 1999/12/29 05:05:33 peter Exp $";
#endif /* not lint */

#define KERNEL
extern int errno;
#include <sys/errno.h>
#undef KERNEL
#include <sys/param.h>
#include <sys/errno.h>
#include <sys/time.h>
#include <sys/uio.h>
#include <sys/ktrace.h>
#include <sys/ioctl.h>
#include <sys/ptrace.h>
#include <err.h>
#include <locale.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <vis.h>
#include "ktrace.h"

int timestamp, decimal, fancy = 1, tail, maxdata;
char *tracefile = DEF_TRACEFILE;
struct ktr_header ktr_header;

#define eqs(s1, s2)	(strcmp((s1), (s2)) == 0)

main(argc, argv)
	int argc;
	char *argv[];
{
	int ch, ktrlen, size;
	register void *m;
	int trpoints = ALL_POINTS;

	(void) setlocale(LC_CTYPE, "");

	while ((ch = getopt(argc,argv,"f:dlm:nRTt:")) != -1)
		switch((char)ch) {
		case 'f':
			tracefile = optarg;
			break;
		case 'd':
			decimal = 1;
			break;
		case 'l':
			tail = 1;
			break;
		case 'm':
			maxdata = atoi(optarg);
			break;
		case 'n':
			fancy = 0;
			break;
		case 'R':
			timestamp = 2;	/* relative timestamp */
			break;
		case 'T':
			timestamp = 1;
			break;
		case 't':
			trpoints = getpoints(optarg);
			if (trpoints < 0)
				errx(1, "unknown trace point in %s", optarg);
			break;
		default:
			usage();
		}

	if (argc > optind)
		usage();

	m = (void *)malloc(size = 1025);
	if (m == NULL)
		errx(1, "%s", strerror(ENOMEM));
	if (!freopen(tracefile, "r", stdin))
		err(1, "%s", tracefile);
	while (fread_tail(&ktr_header, sizeof(struct ktr_header), 1)) {
		if (trpoints & (1<<ktr_header.ktr_type))
			dumpheader(&ktr_header);
		if ((ktrlen = ktr_header.ktr_len) < 0)
			errx(1, "bogus length 0x%x", ktrlen);
		if (ktrlen > size) {
			m = (void *)realloc(m, ktrlen+1);
			if (m == NULL)
				errx(1, "%s", strerror(ENOMEM));
			size = ktrlen;
		}
		if (ktrlen && fread_tail(m, ktrlen, 1) == 0)
			errx(1, "data too short");
		if ((trpoints & (1<<ktr_header.ktr_type)) == 0)
			continue;
		switch (ktr_header.ktr_type) {
		case KTR_SYSCALL:
			ktrsyscall((struct ktr_syscall *)m);
			break;
		case KTR_SYSRET:
			ktrsysret((struct ktr_sysret *)m);
			break;
		case KTR_NAMEI:
			ktrnamei(m, ktrlen);
			break;
		case KTR_GENIO:
			ktrgenio((struct ktr_genio *)m, ktrlen);
			break;
		case KTR_PSIG:
			ktrpsig((struct ktr_psig *)m);
			break;
		case KTR_CSW:
			ktrcsw((struct ktr_csw *)m);
			break;
		case KTR_USER:
			ktruser(ktrlen, m);
			break;
		}
		if (tail)
			(void)fflush(stdout);
	}
}

fread_tail(buf, size, num)
	char *buf;
	int num, size;
{
	int i;

	while ((i = fread(buf, size, num, stdin)) == 0 && tail) {
		(void)sleep(1);
		clearerr(stdin);
	}
	return (i);
}

dumpheader(kth)
	struct ktr_header *kth;
{
	static char unknown[64];
	static struct timeval prevtime, temp;
	char *type;

	switch (kth->ktr_type) {
	case KTR_SYSCALL:
		type = "CALL";
		break;
	case KTR_SYSRET:
		type = "RET ";
		break;
	case KTR_NAMEI:
		type = "NAMI";
		break;
	case KTR_GENIO:
		type = "GIO ";
		break;
	case KTR_PSIG:
		type = "PSIG";
		break;
	case KTR_CSW:
		type = "CSW";
		break;
	case KTR_USER:
		type = "USER";
		break;
	default:
		(void)sprintf(unknown, "UNKNOWN(%d)", kth->ktr_type);
		type = unknown;
	}

	(void)printf("%6d %-8.*s ", kth->ktr_pid, MAXCOMLEN, kth->ktr_comm);
	if (timestamp) {
		if (timestamp == 2) {
			temp = kth->ktr_time;
			timevalsub(&kth->ktr_time, &prevtime);
			prevtime = temp;
		}
		(void)printf("%ld.%06ld ",
		    kth->ktr_time.tv_sec, kth->ktr_time.tv_usec);
	}
	(void)printf("%s  ", type);
}

#include <sys/syscall.h>
#include "syscalls.c"
int nsyscalls = sizeof (syscallnames) / sizeof (syscallnames[0]);

static char *ptrace_ops[] = {
	"PT_TRACE_ME",	"PT_READ_I",	"PT_READ_D",	"PT_READ_U",
	"PT_WRITE_I",	"PT_WRITE_D",	"PT_WRITE_U",	"PT_CONTINUE",
	"PT_KILL",	"PT_STEP",	"PT_ATTACH",	"PT_DETACH",
};

ktrsyscall(ktr)
	register struct ktr_syscall *ktr;
{
	register narg = ktr->ktr_narg;
	register register_t *ip;
	char *ioctlname();

	if (ktr->ktr_code >= nsyscalls || ktr->ktr_code < 0)
		(void)printf("[%d]", ktr->ktr_code);
	else
		(void)printf("%s", syscallnames[ktr->ktr_code]);
	ip = &ktr->ktr_args[0];
	if (narg) {
		char c = '(';
		if (fancy) {
			if (ktr->ktr_code == SYS_ioctl) {
				char *cp;
				if (decimal)
					(void)printf("(%ld", (long)*ip);
				else
					(void)printf("(%#lx", (long)*ip);
				ip++;
				narg--;
				if ((cp = ioctlname(*ip)) != NULL)
					(void)printf(",%s", cp);
				else {
					if (decimal)
						(void)printf(",%ld", (long)*ip);
					else
						(void)printf(",%#lx ", (long)*ip);
				}
				c = ',';
				ip++;
				narg--;
			} else if (ktr->ktr_code == SYS_ptrace) {
				if (*ip < sizeof(ptrace_ops) /
				    sizeof(ptrace_ops[0]) && *ip >= 0)
					(void)printf("(%s", ptrace_ops[*ip]);
#ifdef PT_GETREGS
				else if (*ip == PT_GETREGS)
					(void)printf("(%s", "PT_GETREGS");
#endif
#ifdef PT_SETREGS
				else if (*ip == PT_SETREGS)
					(void)printf("(%s", "PT_SETREGS");
#endif
#ifdef PT_GETFPREGS
				else if (*ip == PT_GETFPREGS)
					(void)printf("(%s", "PT_GETFPREGS");
#endif
#ifdef PT_SETFPREGS
				else if (*ip == PT_SETFPREGS)
					(void)printf("(%s", "PT_SETFPREGS");
#endif
#ifdef PT_GETDBREGS
				else if (*ip == PT_GETDBREGS)
					(void)printf("(%s", "PT_GETDBREGS");
#endif
#ifdef PT_SETDBREGS
				else if (*ip == PT_SETDBREGS)
					(void)printf("(%s", "PT_SETDBREGS");
#endif
				else
					(void)printf("(%ld", (long)*ip);
				c = ',';
				ip++;
				narg--;
			}
		}
		while (narg) {
			if (decimal)
				(void)printf("%c%ld", c, (long)*ip);
			else
				(void)printf("%c%#lx", c, (long)*ip);
			c = ',';
			ip++;
			narg--;
		}
		(void)putchar(')');
	}
	(void)putchar('\n');
}

ktrsysret(ktr)
	struct ktr_sysret *ktr;
{
	register register_t ret = ktr->ktr_retval;
	register int error = ktr->ktr_error;
	register int code = ktr->ktr_code;

	if (code >= nsyscalls || code < 0)
		(void)printf("[%d] ", code);
	else
		(void)printf("%s ", syscallnames[code]);

	if (error == 0) {
		if (fancy) {
			(void)printf("%d", ret);
			if (ret < 0 || ret > 9)
				(void)printf("/%#lx", (long)ret);
		} else {
			if (decimal)
				(void)printf("%ld", (long)ret);
			else
				(void)printf("%#lx", (long)ret);
		}
	} else if (error == ERESTART)
		(void)printf("RESTART");
	else if (error == EJUSTRETURN)
		(void)printf("JUSTRETURN");
	else {
		(void)printf("-1 errno %d", ktr->ktr_error);
		if (fancy)
			(void)printf(" %s", strerror(ktr->ktr_error));
	}
	(void)putchar('\n');
}

ktrnamei(cp, len)
	char *cp;
{
	(void)printf("\"%.*s\"\n", len, cp);
}

ktrgenio(ktr, len)
	struct ktr_genio *ktr;
{
	register int datalen = len - sizeof (struct ktr_genio);
	register char *dp = (char *)ktr + sizeof (struct ktr_genio);
	register char *cp;
	register int col = 0;
	register width;
	char visbuf[5];
	static screenwidth = 0;

	if (screenwidth == 0) {
		struct winsize ws;

		if (fancy && ioctl(fileno(stderr), TIOCGWINSZ, &ws) != -1 &&
		    ws.ws_col > 8)
			screenwidth = ws.ws_col;
		else
			screenwidth = 80;
	}
	printf("fd %d %s %d byte%s\n", ktr->ktr_fd,
		ktr->ktr_rw == UIO_READ ? "read" : "wrote", datalen,
		datalen == 1 ? "" : "s");
	if (maxdata && datalen > maxdata)
		datalen = maxdata;
	(void)printf("       \"");
	col = 8;
	for (;datalen > 0; datalen--, dp++) {
		(void) vis(visbuf, *dp, VIS_CSTYLE, *(dp+1));
		cp = visbuf;
		/*
		 * Keep track of printables and
		 * space chars (like fold(1)).
		 */
		if (col == 0) {
			(void)putchar('\t');
			col = 8;
		}
		switch(*cp) {
		case '\n':
			col = 0;
			(void)putchar('\n');
			continue;
		case '\t':
			width = 8 - (col&07);
			break;
		default:
			width = strlen(cp);
		}
		if (col + width > (screenwidth-2)) {
			(void)printf("\\\n\t");
			col = 8;
		}
		col += width;
		do {
			(void)putchar(*cp++);
		} while (*cp);
	}
	if (col == 0)
		(void)printf("       ");
	(void)printf("\"\n");
}

char *signames[] = {
	"NULL", "HUP", "INT", "QUIT", "ILL", "TRAP", "IOT",	/*  1 - 6  */
	"EMT", "FPE", "KILL", "BUS", "SEGV", "SYS",		/*  7 - 12 */
	"PIPE", "ALRM",  "TERM", "URG", "STOP", "TSTP",		/* 13 - 18 */
	"CONT", "CHLD", "TTIN", "TTOU", "IO", "XCPU",		/* 19 - 24 */
	"XFSZ", "VTALRM", "PROF", "WINCH", "29", "USR1",	/* 25 - 30 */
	"USR2", NULL,						/* 31 - 32 */
};

ktrpsig(psig)
	struct ktr_psig *psig;
{
	(void)printf("SIG%s ", signames[psig->signo]);
	if (psig->action == SIG_DFL)
		(void)printf("SIG_DFL\n");
	else
		(void)printf("caught handler=0x%lx mask=0x%x code=0x%x\n",
		    (u_long)psig->action, psig->mask, psig->code);
}

ktrcsw(cs)
	struct ktr_csw *cs;
{
	(void)printf("%s %s\n", cs->out ? "stop" : "resume",
		cs->user ? "user" : "kernel");
}

ktruser(len, p)
	int len;
	unsigned char *p;
{
	(void)printf("%d ", len);
	while (len--)
		(void)printf(" %02x", *p++);
	(void)printf("\n");
		
}

usage()
{
	(void)fprintf(stderr,
	    "usage: kdump [-dnlRT] [-f trfile] [-m maxdata] [-t [cnisuw]]\n");
	exit(1);
}
