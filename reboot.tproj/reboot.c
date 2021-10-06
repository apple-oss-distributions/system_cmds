/*
 * Copyright (c) 1980, 1986, 1993
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
"@(#) Copyright (c) 1980, 1986, 1993\n\
	The Regents of the University of California.  All rights reserved.\n";
#endif /* not lint */

#ifndef lint
#if 0
static char sccsid[] = "@(#)reboot.c	8.1 (Berkeley) 6/5/93";
#endif
static const char rcsid[] =
  "$FreeBSD: src/sbin/reboot/reboot.c,v 1.17 2002/10/06 16:24:36 thomas Exp $";
#endif /* not lint */

#include <sys/reboot.h>
#include <sys/types.h>
#include <sys/sysctl.h>
#include <signal.h>
#include <err.h>
#include <errno.h>
#include <fcntl.h>
#include <util.h>
#include <pwd.h>
#include <syslog.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#ifdef __APPLE__
#include "kextmanager.h"
#include <IOKit/kext/kextmanager_types.h>
#include <mach/mach_port.h>		// allocate
#include <mach/mach.h>			// task_self, etc
#include <servers/bootstrap.h>	// bootstrap
#endif

void usage(void);
u_int get_pageins(void);
#ifdef __APPLE__
int reserve_reboot(void);
#endif

int dohalt;

int
main(int argc, char *argv[])
{
	struct passwd *pw;
	int ch, howto, i, fd, kflag, lflag, nflag, qflag, pflag, uflag, sverrno;
	u_int pageins;
	char *kernel, *p;
	const char *user;

	if (strstr((p = rindex(*argv, '/')) ? p + 1 : *argv, "halt")) {
		dohalt = 1;
		howto = RB_HALT;
	} else
		howto = 0;
	kflag = lflag = nflag = qflag = 0;
#ifndef __APPLE__
	while ((ch = getopt(argc, argv, "dk:lnpq")) != -1)
#else
	while ((ch = getopt(argc, argv, "lnqu")) != -1)
#endif
		switch(ch) {
#ifndef __APPLE__
		case 'd':
			howto |= RB_DUMP;
			break;
		case 'k':
			kflag = 1;
			kernel = optarg;
			break;
#endif
		case 'l':
			lflag = 1;
			break;
		case 'n':
			nflag = 1;
			howto |= RB_NOSYNC;
			break;
/* -p is irrelevant on OS X.  It does that anyway. */
#ifndef __APPLE__
		case 'p':
			pflag = 1;
			howto |= RB_POWEROFF;
			break;
#endif
		case 'u':
			uflag = 1;
			howto |= RB_UPSDELAY;
			break;
		case 'q':
			qflag = 1;
			break;
		case '?':
		default:
			usage();
		}
	argc -= optind;
	argv += optind;

#ifndef __APPLE__
	if ((howto & (RB_DUMP | RB_HALT)) == (RB_DUMP | RB_HALT))
		errx(1, "cannot dump (-d) when halting; must reboot instead");
#endif
	if (geteuid()) {
		errno = EPERM;
		err(1, NULL);
	}

#ifdef __APPLE__
	if (!lflag) {	// shutdown(8) has already checked w/kextd
		if ((errno = reserve_reboot()) && !qflag)
			err(1, "couldn't lock for reboot");
	}
#endif

	if (qflag) {
		reboot(howto);
		err(1, NULL);
	}

#ifndef __APPLE__
	if (kflag) {
		fd = open("/boot/nextboot.conf", O_WRONLY | O_CREAT, 0444);
		if (fd > -1) {
			(void)write(fd, "nextboot_enable=\"YES\"\n", 22);
			(void)write(fd, "kernel=\"", 8L);
			(void)write(fd, kernel, strlen(kernel));
			(void)write(fd, "\"\n", 2);
			close(fd);
		}
	}
#endif

	/* Log the reboot. */
	if (!lflag)  {
		if ((user = getlogin()) == NULL)
			user = (pw = getpwuid(getuid())) ?
			    pw->pw_name : "???";
		if (dohalt) {
			openlog("halt", 0, LOG_AUTH | LOG_CONS);
			syslog(LOG_CRIT, "halted by %s%s", user, 
			     (howto & RB_UPSDELAY) ? " with UPS delay":"");
		} else {
			openlog("reboot", 0, LOG_AUTH | LOG_CONS);
			syslog(LOG_CRIT, "rebooted by %s", user);
		}
	}
	logwtmp("~", "shutdown", "");

	/*
	 * Do a sync early on, so disks start transfers while we're off
	 * killing processes.  Don't worry about writes done before the
	 * processes die, the reboot system call syncs the disks.
	 */
	if (!nflag)
		sync();

	/* Just stop init -- if we fail, we'll restart it. */
	if (kill(1, SIGTSTP) == -1)
		err(1, "SIGTSTP init");

	/* Ignore the SIGHUP we get when our parent shell dies. */
	(void)signal(SIGHUP, SIG_IGN);

#ifndef __APPLE__
	/* Send a SIGTERM first, a chance to save the buffers. */
	if (kill(-1, SIGTERM) == -1)
		err(1, "SIGTERM processes");

	/*
	 * After the processes receive the signal, start the rest of the
	 * buffers on their way.  Wait 5 seconds between the SIGTERM and
	 * the SIGKILL to give everybody a chance. If there is a lot of
	 * paging activity then wait longer, up to a maximum of approx
	 * 60 seconds.
	 */
	sleep(2);
	for (i = 0; i < 20; i++) {
		pageins = get_pageins();
		if (!nflag)
			sync();
		sleep(3);
		if (get_pageins() == pageins)
			break;
	}

	for (i = 1;; ++i) {
		if (kill(-1, SIGKILL) == -1) {
			if (errno == ESRCH)
				break;
			goto restart;
		}
		if (i > 5) {
			(void)fprintf(stderr,
			    "WARNING: some process(es) wouldn't die\n");
			break;
		}
		(void)sleep(2 * i);
	}
#endif

	reboot(howto);
	/* FALLTHROUGH */

#ifndef __APPLE__
restart:
#endif
	sverrno = errno;
	errx(1, "%s%s", kill(1, SIGHUP) == -1 ? "(can't restart init): " : "",
	    strerror(sverrno));
	/* NOTREACHED */
}

void
usage()
{
#ifndef __APPLE__
	(void)fprintf(stderr, "usage: %s [-dnpq] [-k kernel]\n",
#else
	(void)fprintf(stderr, "usage: %s [-lnq]\n",
#endif
	    dohalt ? "halt" : "reboot");
	exit(1);
}

u_int
get_pageins()
{
	u_int pageins;
	size_t len;

	len = sizeof(pageins);
	if (sysctlbyname("vm.stats.vm.v_swappgsin", &pageins, &len, NULL, 0)
	    != 0) {
		warnx("v_swappgsin");
		return (0);
	}
	return pageins;
}

#ifdef __APPLE__
// XX another copy of this routine is in shutdown.c; it would be nice to share

#define LCK_MAXTRIES 10
#define LCK_DELAY	 30
/*
 * contact kextd to lock for reboot
 */
int
reserve_reboot()
{
	int rval = ELAST+1;
	kern_return_t macherr = KERN_FAILURE;
	mach_port_t tport, bsport, kxport, myport = MACH_PORT_NULL;
	int busyStatus, nretries = LCK_MAXTRIES;
	dev_path_t busyDev = "<unknown>";

	// find kextd
	tport = mach_task_self();
	if (tport == MACH_PORT_NULL)  goto finish;
	macherr = task_get_bootstrap_port(tport, &bsport);
	if (macherr)  goto finish;
	macherr = bootstrap_look_up(bsport, KEXTD_SERVER_NAME, &kxport);
	if (macherr)  goto finish;

	// allocate a port to pass to kextd (in case we die)
	macherr = mach_port_allocate(tport, MACH_PORT_RIGHT_RECEIVE, &myport);
	if (macherr)  goto finish;

	// loop trying to lock for reboot (i.e. no volumes are busy)
	do {
		nretries--;
		macherr = kextmanager_lock_reboot(kxport, myport, busyDev, &busyStatus);
		if (macherr)  goto finish;

		if (busyStatus == EBUSY) {
			if (*busyDev) {
				warnx("%s is busy updating; delaying reboot (%d retries left)",
						busyDev, nretries);
			} else
				warnx("kextd still starting up");
			if (nretries)		sleep(LCK_DELAY);	// don't sleep the last time
		}
	} while (busyStatus == EBUSY && nretries > 0);

	rval = busyStatus;

finish:
	if (macherr == BOOTSTRAP_UNKNOWN_SERVICE) {
		mach_port_mod_refs(tport, myport, MACH_PORT_RIGHT_RECEIVE, -1);
		rval = 0;
	} else if (macherr) {
		warnx("couldn't lock kext manager for reboot: %s",
				mach_error_string(macherr));
		rval = ELAST + 1;
	}
	if (rval && myport != MACH_PORT_NULL) {
		mach_port_mod_refs(tport, myport, MACH_PORT_RIGHT_RECEIVE, -1);
	}

	return rval;
}
#endif
