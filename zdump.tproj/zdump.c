/*
 * Copyright (c) 1999 Apple Computer, Inc. All rights reserved.
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
#if defined(LIBC_SCCS) && !defined(lint)
#if 0
static char	elsieid[] = "@(#)zdump.c	7.24";
#else
static char rcsid[] = "$OpenBSD: zdump.c,v 1.5 1997/01/21 04:52:45 millert Exp $";
#endif
#endif /* LIBC_SCCS and not lint */

/*
** This code has been made independent of the rest of the time
** conversion package to increase confidence in the verification it provides.
** You can use this code to help in verifying other implementations.
*/

#include "stdio.h"	/* for stdout, stderr, perror */
#include "string.h"	/* for strcpy */
#include "sys/types.h"	/* for time_t */
#include "time.h"	/* for struct tm */
#include "stdlib.h"	/* for exit, malloc, atoi */

#ifndef MAX_STRING_LENGTH
#define MAX_STRING_LENGTH	1024
#endif /* !defined MAX_STRING_LENGTH */

#ifndef TRUE
#define TRUE		1
#endif /* !defined TRUE */

#ifndef FALSE
#define FALSE		0
#endif /* !defined FALSE */

#ifndef EXIT_SUCCESS
#define EXIT_SUCCESS	0
#endif /* !defined EXIT_SUCCESS */

#ifndef EXIT_FAILURE
#define EXIT_FAILURE	1
#endif /* !defined EXIT_FAILURE */

#ifndef SECSPERMIN
#define SECSPERMIN	60
#endif /* !defined SECSPERMIN */

#ifndef MINSPERHOUR
#define MINSPERHOUR	60
#endif /* !defined MINSPERHOUR */

#ifndef SECSPERHOUR
#define SECSPERHOUR	(SECSPERMIN * MINSPERHOUR)
#endif /* !defined SECSPERHOUR */

#ifndef HOURSPERDAY
#define HOURSPERDAY	24
#endif /* !defined HOURSPERDAY */

#ifndef EPOCH_YEAR
#define EPOCH_YEAR	1970
#endif /* !defined EPOCH_YEAR */

#ifndef TM_YEAR_BASE
#define TM_YEAR_BASE	1900
#endif /* !defined TM_YEAR_BASE */

#ifndef DAYSPERNYEAR
#define DAYSPERNYEAR	365
#endif /* !defined DAYSPERNYEAR */

#ifndef isleap
#define isleap(y) ((((y) % 4) == 0 && ((y) % 100) != 0) || ((y) % 400) == 0)
#endif /* !defined isleap */

#if HAVE_GETTEXT - 0
#include "locale.h"	/* for setlocale */
#include "libintl.h"
#endif /* HAVE_GETTEXT - 0 */

#ifndef GNUC_or_lint
#ifdef lint
#define GNUC_or_lint
#endif /* defined lint */
#ifndef lint
#ifdef __GNUC__
#define GNUC_or_lint
#endif /* defined __GNUC__ */
#endif /* !defined lint */
#endif /* !defined GNUC_or_lint */

#ifndef INITIALIZE
#ifdef GNUC_or_lint
#define INITIALIZE(x)	((x) = 0)
#endif /* defined GNUC_or_lint */
#ifndef GNUC_or_lint
#define INITIALIZE(x)
#endif /* !defined GNUC_or_lint */
#endif /* !defined INITIALIZE */

/*
** For the benefit of GNU folk...
** `_(MSGID)' uses the current locale's message library string for MSGID.
** The default is to use gettext if available, and use MSGID otherwise.
*/

#ifndef _
#if HAVE_GETTEXT - 0
#define _(msgid) gettext(msgid)
#else /* !(HAVE_GETTEXT - 0) */
#define _(msgid) msgid
#endif /* !(HAVE_GETTEXT - 0) */
#endif /* !defined _ */

#ifndef TZ_DOMAIN
#define TZ_DOMAIN "tz"
#endif /* !defined TZ_DOMAIN */

extern char **	environ;
extern int	getopt();
extern char *	optarg;
extern int	optind;
extern time_t	time();
extern char *	tzname[2];

static char *	abbr();
static long	delta();
static time_t	hunt();
static int	longest;
static char *	progname;
static void	show();

int
main(argc, argv)
int	argc;
char *	argv[];
{
	register int		i;
	register int		c;
	register int		vflag;
	register char *		cutoff;
	register int		cutyear;
	register long		cuttime;
	char **			fakeenv;
	time_t			now;
	time_t			t;
	time_t			newt;
	time_t			hibit;
	struct tm		tm;
	struct tm		newtm;

	INITIALIZE(cuttime);
#if HAVE_GETTEXT - 0
	(void) setlocale(LC_MESSAGES, "");
#ifdef TZ_DOMAINDIR
	(void) bindtextdomain(TZ_DOMAIN, TZ_DOMAINDIR);
#endif /* defined(TEXTDOMAINDIR) */
	(void) textdomain(TZ_DOMAIN);
#endif /* HAVE_GETTEXT - 0 */
	progname = argv[0];
	vflag = 0;
	cutoff = NULL;
	while ((c = getopt(argc, argv, "c:v")) == 'c' || c == 'v')
		if (c == 'v')
			vflag = 1;
		else	cutoff = optarg;
	if (c != EOF ||
		(optind == argc - 1 && strcmp(argv[optind], "=") == 0)) {
			(void) fprintf(stderr,
_("%s: usage is %s [ -v ] [ -c cutoff ] zonename ...\n"),
				argv[0], argv[0]);
			(void) exit(EXIT_FAILURE);
	}
	if (cutoff != NULL) {
		int	y;

		cutyear = atoi(cutoff);
		cuttime = 0;
		for (y = EPOCH_YEAR; y < cutyear; ++y)
			cuttime += DAYSPERNYEAR + isleap(y);
		cuttime *= SECSPERHOUR * HOURSPERDAY;
	}
	(void) time(&now);
	longest = 0;
	for (i = optind; i < argc; ++i)
		if (strlen(argv[i]) > longest)
			longest = strlen(argv[i]);
	for (hibit = 1; (hibit << 1) != 0; hibit <<= 1)
		continue;
	{
		register int	from;
		register int	to;

		for (i = 0;  environ[i] != NULL;  ++i)
			continue;
		fakeenv = (char **) malloc((size_t) ((i + 2) *
			sizeof *fakeenv));
		if (fakeenv == NULL ||
			(fakeenv[0] = (char *) malloc((size_t) (longest +
				4))) == NULL) {
					(void) perror(progname);
					(void) exit(EXIT_FAILURE);
		}
		to = 0;
		(void) strcpy(fakeenv[to++], "TZ=");
		for (from = 0; environ[from] != NULL; ++from)
			if (strncmp(environ[from], "TZ=", 3) != 0)
				fakeenv[to++] = environ[from];
		fakeenv[to] = NULL;
		environ = fakeenv;
	}
	for (i = optind; i < argc; ++i) {
		static char	buf[MAX_STRING_LENGTH];

		(void) strcpy(&fakeenv[0][3], argv[i]);
		show(argv[i], now, FALSE);
		if (!vflag)
			continue;
		/*
		** Get lowest value of t.
		*/
		t = hibit;
		if (t > 0)		/* time_t is unsigned */
			t = 0;
		show(argv[i], t, TRUE);
		t += SECSPERHOUR * HOURSPERDAY;
		show(argv[i], t, TRUE);
		tm = *localtime(&t);
		(void) strncpy(buf, abbr(&tm), (sizeof buf) - 1);
		for ( ; ; ) {
			if (cutoff != NULL && t >= cuttime)
				break;
			newt = t + SECSPERHOUR * 12;
			if (cutoff != NULL && newt >= cuttime)
				break;
			if (newt <= t)
				break;
			newtm = *localtime(&newt);
			if (delta(&newtm, &tm) != (newt - t) ||
				newtm.tm_isdst != tm.tm_isdst ||
				strcmp(abbr(&newtm), buf) != 0) {
					newt = hunt(argv[i], t, newt);
					newtm = *localtime(&newt);
					(void) strncpy(buf, abbr(&newtm),
						(sizeof buf) - 1);
			}
			t = newt;
			tm = newtm;
		}
		/*
		** Get highest value of t.
		*/
		t = ~((time_t) 0);
		if (t < 0)		/* time_t is signed */
			t &= ~hibit;
		t -= SECSPERHOUR * HOURSPERDAY;
		show(argv[i], t, TRUE);
		t += SECSPERHOUR * HOURSPERDAY;
		show(argv[i], t, TRUE);
	}
	if (fflush(stdout) || ferror(stdout)) {
		(void) fprintf(stderr, _("%s: Error writing standard output "),
			argv[0]);
		(void) perror(_("standard output"));
		(void) exit(EXIT_FAILURE);
	}
	exit(EXIT_SUCCESS);

	/* gcc -Wall pacifier */
	for ( ; ; )
		continue;
}

static time_t
hunt(name, lot, hit)
char *	name;
time_t	lot;
time_t	hit;
{
	time_t		t;
	struct tm	lotm;
	struct tm	tm;
	static char	loab[MAX_STRING_LENGTH];

	lotm = *localtime(&lot);
	(void) strncpy(loab, abbr(&lotm), (sizeof loab) - 1);
	loab[(sizeof loab) - 1] = '\0';
	while ((hit - lot) >= 2) {
		t = lot / 2 + hit / 2;
		if (t <= lot)
			++t;
		else if (t >= hit)
			--t;
		tm = *localtime(&t);
		if (delta(&tm, &lotm) == (t - lot) &&
			tm.tm_isdst == lotm.tm_isdst &&
			strcmp(abbr(&tm), loab) == 0) {
				lot = t;
				lotm = tm;
		} else	hit = t;
	}
	show(name, lot, TRUE);
	show(name, hit, TRUE);
	return hit;
}

/*
** Thanks to Paul Eggert (eggert@twinsun.com) for logic used in delta.
*/

static long
delta(newp, oldp)
struct tm *	newp;
struct tm *	oldp;
{
	long	result;
	int	tmy;

	if (newp->tm_year < oldp->tm_year)
		return -delta(oldp, newp);
	result = 0;
	for (tmy = oldp->tm_year; tmy < newp->tm_year; ++tmy)
		result += DAYSPERNYEAR + isleap(tmy + TM_YEAR_BASE);
	result += newp->tm_yday - oldp->tm_yday;
	result *= HOURSPERDAY;
	result += newp->tm_hour - oldp->tm_hour;
	result *= MINSPERHOUR;
	result += newp->tm_min - oldp->tm_min;
	result *= SECSPERMIN;
	result += newp->tm_sec - oldp->tm_sec;
	return result;
}

extern struct tm *	localtime();

static void
show(zone, t, v)
char *	zone;
time_t	t;
int	v;
{
	struct tm *	tmp;

	(void) printf("%-*s  ", longest, zone);
	if (v)
		(void) printf("%.24s GMT = ", asctime(gmtime(&t)));
	tmp = localtime(&t);
	(void) printf("%.24s", asctime(tmp));
	if (*abbr(tmp) != '\0')
		(void) printf(" %s", abbr(tmp));
	if (v) {
		(void) printf(" isdst=%d", tmp->tm_isdst);
#ifdef TM_GMTOFF
		(void) printf(" gmtoff=%ld", tmp->TM_GMTOFF);
#endif /* defined TM_GMTOFF */
	}
	(void) printf("\n");
}

static char *
abbr(tmp)
struct tm *	tmp;
{
	register char *	result;
	static char	nada;

	if (tmp->tm_isdst != 0 && tmp->tm_isdst != 1)
		return &nada;
	result = tzname[tmp->tm_isdst];
	return (result == NULL) ? &nada : result;
}
