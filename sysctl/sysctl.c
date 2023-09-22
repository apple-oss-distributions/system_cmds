/*
 * Copyright (c) 1993
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

#include <sys/cdefs.h>
#ifndef lint
__unused static const char copyright[] =
"@(#) Copyright (c) 1993\n\
	The Regents of the University of California.  All rights reserved.\n";
#endif /* not lint */

#ifndef lint
#if 0
static char sccsid[] = "@(#)from: sysctl.c	8.1 (Berkeley) 6/6/93";
#endif
__unused static const char rcsid[] =
  "$FreeBSD$";
#endif /* not lint */

#include <sys/param.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/sysctl.h>
#ifdef __APPLE__
#include <mach/machine/vm_param.h>
#include <mach/machine/vm_types.h>
#include <mach/mach_types.h>
#else // !__APPLE__
#include <sys/vmmeter.h>
#endif // !__APPLE__

#include <ctype.h>
#include <err.h>
#include <errno.h>
#include <inttypes.h>
#include <locale.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static int	aflag, bflag, dflag, eflag, hflag, iflag;
static int	Nflag, nflag, oflag, qflag, xflag, warncount;

static int	oidfmt(int *, int, char *, u_int *);
static void	parse(const char *);
#ifdef __APPLE__
static int	show_var(int *, int, int);
#else
static int	show_var(int *, int);
#endif
static int	sysctl_all(int *oid, int len);
static int	name2oid(char *, int *);

#ifndef __APPLE__
static int	set_IK(const char *, int *);
#endif

#ifdef __APPLE__
// Shims for FreeBSD source compatibility.
#define CTLTYPE_UINT 0xa
#define CTLTYPE_LONG 0xb
#define CTLTYPE_ULONG 0xc
#define CTLTYPE_S64 0xd
#define CTLTYPE_U64 0xe

#define CTLFLAG_TUN 0

// Support for CTL_USER
const struct ctlname names[] = CTL_NAMES;
const struct ctlname user_names[] = CTL_USER_NAMES;
const int user_names_count = sizeof(user_names) / sizeof(*user_names);
#endif

static void
usage(void)
{

	(void)fprintf(stderr, "%s\n%s\n",
	    "usage: sysctl [-bdehiNnoqx] name[=value] ...",
	    "       sysctl [-bdehNnoqx] -a");
	exit(1);
}

int
main(int argc, char **argv)
{
	int ch;

	setlocale(LC_NUMERIC, "");
	setbuf(stdout,0);
	setbuf(stderr,0);

	while ((ch = getopt(argc, argv, "AabdehiNnoqwxX")) != -1) {
		switch (ch) {
		case 'A':
			/* compatibility */
			aflag = oflag = 1;
			break;
		case 'a':
			aflag = 1;
			break;
		case 'b':
			bflag = 1;
			break;
		case 'd':
			dflag = 1;
			break;
		case 'e':
			eflag = 1;
			break;
		case 'h':
			hflag = 1;
			break;
		case 'i':
			iflag = 1;
			break;
		case 'N':
			Nflag = 1;
			break;
		case 'n':
			nflag = 1;
			break;
		case 'o':
			oflag = 1;
			break;
		case 'q':
			qflag = 1;
			break;
		case 'w':
			/* compatibility */
			/* ignored */
			break;
		case 'X':
			/* compatibility */
			aflag = xflag = 1;
			break;
		case 'x':
			xflag = 1;
			break;
		default:
			usage();
		}
	}
	argc -= optind;
	argv += optind;

	if (Nflag && nflag)
		usage();
	if (aflag && argc == 0)
		exit(sysctl_all(0, 0));
	if (argc == 0)
		usage();

	warncount = 0;
	while (argc-- > 0)
		parse(*argv++);
	exit(warncount);
}

/*
 * Parse a name into a MIB entry.
 * Lookup and print out the MIB entry if it exists.
 * Set a new value if requested.
 */
static void
parse(const char *string)
{
	int len, i, j;
	void *newval = 0;
	int intval;
	unsigned int uintval;
	long longval;
	unsigned long ulongval;
	size_t newsize = 0;
	int64_t i64val;
	uint64_t u64val;
	int mib[CTL_MAXNAME];
	char *cp, *bufp, buf[BUFSIZ], *endptr, fmt[BUFSIZ];
	u_int kind;

	cp = buf;
	if (snprintf(buf, BUFSIZ, "%s", string) >= BUFSIZ)
		errx(1, "oid too long: '%s'", string);
	bufp = strsep(&cp, "=");
	if (cp != NULL) {
		while (isspace(*cp))
			cp++;
		newval = cp;
	}
	len = name2oid(bufp, mib);

	if (len < 0) {
		if (iflag)
			return;
		if (qflag)
			exit(1);
		else
			errx(1, "unknown oid '%s'", bufp);
	}

	if (oidfmt(mib, len, fmt, &kind))
		err(1, "couldn't find format of oid '%s'", bufp);

	if (newval == NULL || dflag) {
		if ((kind & CTLTYPE) == CTLTYPE_NODE) {
			if (dflag) {
#ifdef __APPLE__
				i = show_var(mib, len, 1);
#else
				i = show_var(mib, len);
#endif
				if (!i && !bflag)
					putchar('\n');
			}
			sysctl_all(mib, len);
		} else {
#ifdef __APPLE__
			i = show_var(mib, len, 1);
#else
			i = show_var(mib, len);
#endif
			if (!i && !bflag)
				putchar('\n');
		}
	} else {
		if ((kind & CTLTYPE) == CTLTYPE_NODE)
			errx(1, "oid '%s' isn't a leaf node", bufp);

		if (!(kind & CTLFLAG_WR)) {
			errx(1, "oid '%s' is read only", bufp);
		}

		if ((kind & CTLTYPE) == CTLTYPE_INT ||
		    (kind & CTLTYPE) == CTLTYPE_UINT ||
		    (kind & CTLTYPE) == CTLTYPE_LONG ||
		    (kind & CTLTYPE) == CTLTYPE_ULONG ||
		    (kind & CTLTYPE) == CTLTYPE_S64 ||
		    (kind & CTLTYPE) == CTLTYPE_U64) {
			if (strlen(newval) == 0)
				errx(1, "empty numeric value");
		}

		switch (kind & CTLTYPE) {
			case CTLTYPE_INT:
				if (strcmp(fmt, "IK") == 0) {
#ifndef __APPLE__
					if (!set_IK(newval, &intval))
#endif
						errx(1, "invalid value '%s'",
						    (char *)newval);
 				} else {
					intval = (int)strtol(newval, &endptr,
					    0);
					if (endptr == newval || *endptr != '\0')
						errx(1, "invalid integer '%s'",
						    (char *)newval);
				}
				newval = &intval;
				newsize = sizeof(intval);
				break;
			case CTLTYPE_UINT:
				uintval = (int) strtoul(newval, &endptr, 0);
				if (endptr == newval || *endptr != '\0')
					errx(1, "invalid unsigned integer '%s'",
					    (char *)newval);
				newval = &uintval;
				newsize = sizeof(uintval);
				break;
			case CTLTYPE_LONG:
				longval = strtol(newval, &endptr, 0);
				if (endptr == newval || *endptr != '\0')
					errx(1, "invalid long integer '%s'",
					    (char *)newval);
				newval = &longval;
				newsize = sizeof(longval);
				break;
			case CTLTYPE_ULONG:
				ulongval = strtoul(newval, &endptr, 0);
				if (endptr == newval || *endptr != '\0')
					errx(1, "invalid unsigned long integer"
					    " '%s'", (char *)newval);
				newval = &ulongval;
				newsize = sizeof(ulongval);
				break;
			case CTLTYPE_STRING:
				/* One extra byte for the NUL terminator */
				newsize = strlen(newval) + 1;
				break;
			case CTLTYPE_S64:
				i64val = strtoimax(newval, &endptr, 0);
				if (endptr == newval || *endptr != '\0')
					errx(1, "invalid int64_t '%s'",
					    (char *)newval);
				newval = &i64val;
				newsize = sizeof(i64val);
				break;
			case CTLTYPE_U64:
				u64val = strtoumax(newval, &endptr, 0);
				if (endptr == newval || *endptr != '\0')
					errx(1, "invalid uint64_t '%s'",
					    (char *)newval);
				newval = &u64val;
				newsize = sizeof(u64val);
				break;
			case CTLTYPE_OPAQUE:
				/* FALLTHROUGH */
			default:
				errx(1, "oid '%s' is type %d,"
					" cannot set that", bufp,
					kind & CTLTYPE);
		}

#ifdef __APPLE__
		i = show_var(mib, len, 1);
#else
		i = show_var(mib, len);
#endif
		if (sysctl(mib, len, 0, 0, newval, newsize) == -1) {
			if (!i && !bflag)
				putchar('\n');
			switch (errno) {
#ifdef __APPLE__
			case ENOTSUP:
#endif // __APPLE__
			case EOPNOTSUPP:
				errx(1, "%s: value is not available",
					string);
			case ENOTDIR:
				errx(1, "%s: specification is incomplete",
					string);
			case ENOMEM:
				errx(1, "%s: type is unknown to this program",
					string);
			default:
				warn("%s", string);
				warncount++;
				return;
			}
		}
		if (!bflag)
			printf(" -> ");
		i = nflag;
		nflag = 1;
#ifdef __APPLE__
		j = show_var(mib, len, 1);
#else
		j = show_var(mib, len);
#endif
		if (!j && !bflag)
			putchar('\n');
		nflag = i;
	}
}

/* These functions will dump out various interesting structures. */

static int
S_clockinfo(int l2, void *p)
{
	struct clockinfo *ci = (struct clockinfo*)p;

	if (l2 != sizeof(*ci)) {
		warnx("S_clockinfo %d != %zu", l2, sizeof(*ci));
		return (1);
	}
#ifdef __APPLE__
	printf(hflag ? "{ hz = %'d, tick = %'d, tickadj = %'d, profhz = %'d, stathz = %'d }" :
	       "{ hz = %d, tick = %d, tickadj = %d, profhz = %d, stathz = %d }",
	       ci->hz, ci->tick, ci->tickadj, ci->profhz, ci->stathz);
#else
	printf(hflag ? "{ hz = %'d, tick = %'d, profhz = %'d, stathz = %'d }" :
		"{ hz = %d, tick = %d, profhz = %d, stathz = %d }",
		ci->hz, ci->tick, ci->profhz, ci->stathz);
#endif
	return (0);
}

static int
S_loadavg(int l2, void *p)
{
	struct loadavg *tv = (struct loadavg*)p;

	if (l2 != sizeof(*tv)) {
		warnx("S_loadavg %d != %zu", l2, sizeof(*tv));
		return (1);
	}
	printf(hflag ? "{ %'.2f %'.2f %'.2f }" : "{ %.2f %.2f %.2f }",
		(double)tv->ldavg[0]/(double)tv->fscale,
		(double)tv->ldavg[1]/(double)tv->fscale,
		(double)tv->ldavg[2]/(double)tv->fscale);
	return (0);
}

static int
S_timeval(int l2, void *p)
{
	struct timeval *tv = (struct timeval*)p;
	time_t tv_sec;
	char *p1, *p2;

	if (l2 != sizeof(*tv)) {
		warnx("S_timeval %d != %zu", l2, sizeof(*tv));
		return (1);
	}
	printf(hflag ? "{ sec = %'jd, usec = %'ld } " :
		"{ sec = %jd, usec = %ld } ",
		(intmax_t)tv->tv_sec, (long)tv->tv_usec);
	tv_sec = tv->tv_sec;
	p1 = strdup(ctime(&tv_sec));
	for (p2=p1; *p2 ; p2++)
		if (*p2 == '\n')
			*p2 = '\0';
	fputs(p1, stdout);
	free(p1);
	return (0);
}

#ifndef __APPLE__
static int
S_vmtotal(int l2, void *p)
{
	struct vmtotal *v = (struct vmtotal *)p;
	int pageKilo = getpagesize() / 1024;

	if (l2 != sizeof(*v)) {
		warnx("S_vmtotal %d != %zu", l2, sizeof(*v));
		return (1);
	}

	printf(
	    "\nSystem wide totals computed every five seconds:"
	    " (values in kilobytes)\n");
	printf("===============================================\n");
	printf(
	    "Processes:\t\t(RUNQ: %hd Disk Wait: %hd Page Wait: "
	    "%hd Sleep: %hd)\n",
	    v->t_rq, v->t_dw, v->t_pw, v->t_sl);
	printf(
	    "Virtual Memory:\t\t(Total: %dK Active: %dK)\n",
	    v->t_vm * pageKilo, v->t_avm * pageKilo);
	printf("Real Memory:\t\t(Total: %dK Active: %dK)\n",
	    v->t_rm * pageKilo, v->t_arm * pageKilo);
	printf("Shared Virtual Memory:\t(Total: %dK Active: %dK)\n",
	    v->t_vmshr * pageKilo, v->t_avmshr * pageKilo);
	printf("Shared Real Memory:\t(Total: %dK Active: %dK)\n",
	    v->t_rmshr * pageKilo, v->t_armshr * pageKilo);
	printf("Free Memory:\t%dK\n", v->t_free * pageKilo);

	return (0);
}

static int
set_IK(const char *str, int *val)
{
	float temp;
	int len, kelv;
	const char *p;
	char *endptr;

	if ((len = strlen(str)) == 0)
		return (0);
	p = &str[len - 1];
	if (*p == 'C' || *p == 'F') {
		temp = strtof(str, &endptr);
		if (endptr == str || endptr != p)
			return (0);
		if (*p == 'F')
			temp = (temp - 32) * 5 / 9;
		kelv = temp * 10 + 2732;
	} else {
		kelv = (int)strtol(str, &endptr, 10);
		if (endptr == str || *endptr != '\0')
			return (0);
	}
	*val = kelv;
	return (1);
}
#endif // !__APPLE__

#ifdef __APPLE__
static int
S_xswusage(int l2, void *p)
{
        struct xsw_usage *xsu = (struct xsw_usage *)p;

	if (l2 != sizeof(*xsu)) {
		warnx("S_xswusage %d != %ld", l2, sizeof(*xsu));
		return (1);
	}
	fprintf(stdout,
		"total = %.2fM  used = %.2fM  free = %.2fM  %s",
		((double)xsu->xsu_total) / (1024.0 * 1024.0),
		((double)xsu->xsu_used) / (1024.0 * 1024.0),
		((double)xsu->xsu_avail) / (1024.0 * 1024.0),
		xsu->xsu_encrypted ? "(encrypted)" : "");
	return (0);
}

static int
T_dev_t(int l2, void *p)
{
	dev_t *d = (dev_t *)p;

	if (l2 != sizeof(*d)) {
		warnx("T_dev_T %d != %ld", l2, sizeof(*d));
		return (1);
	}
	if ((int)(*d) != -1) {
		if (minor(*d) > 255 || minor(*d) < 0)
			printf("{ major = %d, minor = 0x%x }",
				major(*d), minor(*d));
		else
			printf("{ major = %d, minor = %d }",
				major(*d), minor(*d));
	}
	return (0);
}

static int
S_quads(int len, void *p)
{
	size_t size = sizeof(int64_t);
	if (len & (size-1)) {
		return 1;
	}
	while (len > 0) {
		int64_t i = *(int64_t *)p;
		printf("%llu", i);
		if (len > size) {
			len -= size;
			p += size;
			printf(" ");
		} else {
			break;
		}
	}
	return 0;
}
#endif // __APPLE__

/*
 * These functions uses a presently undocumented interface to the kernel
 * to walk the tree and get the type so it can print the value.
 * This interface is under work and consideration, and should probably
 * be killed with a big axe by the first person who can find the time.
 * (be aware though, that the proper interface isn't as obvious as it
 * may seem, there are various conflicting requirements.
 */

static int
name2oid(char *name, int *oidp)
{
	int oid[2];
	int i;
	size_t j;

#ifdef __APPLE__
	// Support for CTL_USER
	const char *user = names[CTL_USER].ctl_name;
	j = strlen(user);
	if (!strncmp(name, user, j)) {
		oidp[0] = CTL_USER;
		if (name[j] == '.') {
			for (i = 1; i < user_names_count; ++i) {
				if (!strcmp(&name[j+1], user_names[i].ctl_name)) {
					oidp[1] = i;
					return 2;
				}
			}
			return -1;
		} else if (name[j] == 0) {
			return 1;
		}
		return -1;
	}
#endif

	oid[0] = 0;
	oid[1] = 3;

	j = CTL_MAXNAME * sizeof(int);
	i = sysctl(oid, 2, oidp, &j, name, strlen(name));
	if (i < 0)
		return (i);
	j /= sizeof(int);
	return (int)j;
}

static int
oidfmt(int *oid, int len, char *fmt, u_int *kind)
{
	int qoid[CTL_MAXNAME+2];
	u_char buf[BUFSIZ];
	int i;
	size_t j;

	qoid[0] = 0;
	qoid[1] = 4;
	memcpy(qoid + 2, oid, len * sizeof(int));

	j = sizeof(buf);
	i = sysctl(qoid, len + 2, buf, &j, 0, 0);
#ifdef __APPLE__
	if (i && errno == ENOENT) {
		// Support for CTL_USER
		if (oid[0] == CTL_USER) {
			if (len == 1) {
				*kind = CTLTYPE_NODE;
				return 0;
			} else if (len == 2 && oid[1] < user_names_count) {
				*kind = user_names[oid[1]].ctl_type;
				return 0;
			}
		}
		return 1;
	}
#endif
	if (i)
		err(1, "sysctl fmt %d %zu %d", i, j, errno);

	if (kind)
#ifdef __APPLE__
		memcpy(kind, buf, sizeof(*kind));
#else
		*kind = *(u_int *)buf;
#endif

	if (fmt)
		strcpy(fmt, (char *)(buf + sizeof(u_int)));

#ifdef __APPLE__
	// Map Darwin sysctl types to FreeBSD types.
	// - 0 with "I" -> CTLTYPE_INT
	// - 0 with "S," -> CTLTYPE_STRUCT
	// - CTLTYPE_INT with "IU" -> CTLTYPE_UINT
	// - CTLTYPE_INT with "L" -> CTLTYPE_LONG
	// - CTLTYPE_QUAD -> CTLTYPE_S64
	// - CTLTYPE_QUAD with "*U" -> CTLTYPE_U64
	if (kind) {
		switch (*kind & CTLTYPE) {
			case 0:
			case CTLTYPE_INT:
				if (buf[sizeof(u_int)] == 'S') {
					*kind = (*kind & ~CTLTYPE) | CTLTYPE_STRUCT;
				} else if (buf[sizeof(u_int)] == 'I') {
					*kind = (*kind & ~CTLTYPE) | CTLTYPE_INT;
					if (buf[sizeof(u_int)+1] == 'U') {
						*kind = (*kind & ~CTLTYPE) | CTLTYPE_UINT;
					}
				} else if (buf[sizeof(u_int)] == 'L') {
					*kind = (*kind & ~CTLTYPE) | CTLTYPE_LONG;
                    if (buf[sizeof(u_int)+1] == 'U') {
                        *kind = (*kind & ~CTLTYPE) | CTLTYPE_ULONG;
                    }
				}
				break;
			case CTLTYPE_QUAD:
				*kind = (*kind & ~CTLTYPE);
				if (fmt && strchr(fmt, 'U')) {
					*kind |= CTLTYPE_U64;
				} else {
					*kind |= CTLTYPE_S64;
				}
				break;
		}
	}
#endif

	return (0);
}

static int ctl_sign[CTLTYPE+1] = {
	[CTLTYPE_INT] = 1,
	[CTLTYPE_LONG] = 1,
	[CTLTYPE_S64] = 1,
};

static int ctl_size[CTLTYPE+1] = {
	[CTLTYPE_INT] = sizeof(int),
	[CTLTYPE_UINT] = sizeof(u_int),
	[CTLTYPE_LONG] = sizeof(long),
	[CTLTYPE_ULONG] = sizeof(u_long),
	[CTLTYPE_S64] = sizeof(int64_t),
	[CTLTYPE_U64] = sizeof(int64_t),
};

/*
 * This formats and outputs the value of one variable
 *
 * Returns zero if anything was actually output.
 * Returns one if didn't know what to do with this.
 * Return minus one if we had errors.
 */
static int
#ifdef __APPLE__
show_var(int *oid, int nlen, int show_masked)
#else
show_var(int *oid, int nlen)
#endif
{
	u_char buf[BUFSIZ], *val, *oval, *p;
	char name[BUFSIZ], *fmt;
	const char *sep, *sep1;
	int qoid[CTL_MAXNAME+2];
	uintmax_t umv;
	intmax_t mv;
	int i, hexlen, sign, ctltype;
	size_t intlen;
	size_t j, len;
	u_int kind;
	int (*func)(int, void *);

	/* Silence GCC. */
	umv = mv = intlen = 0;

	bzero(buf, BUFSIZ);
	bzero(name, BUFSIZ);
	qoid[0] = 0;
	memcpy(qoid + 2, oid, nlen * sizeof(int));
	fmt = (char *)buf;
	oidfmt(oid, nlen, fmt, &kind);

#ifdef __APPLE__
	if (!show_masked && (kind & CTLFLAG_MASKED)) {
		return (1);
	}
#endif

#ifdef __APPLE__
	// Support for CTL_USER
	if (nlen >= 1 && oid[0] == CTL_USER) {
		const char *user_name = "";
		sep = "";
		i = oid[1];
		if (nlen == 2 && i > 0 && i < user_names_count) {
			user_name = user_names[i].ctl_name;
			sep = ".";
		}
		j = snprintf(name, sizeof(name), "%s%s%s",
			     names[CTL_USER].ctl_name, sep, user_name);
		i = 0;
	} else {
#endif
	qoid[1] = 1;
	j = sizeof(name);
	i = sysctl(qoid, nlen + 2, name, &j, 0, 0);
	if (i || !j)
		err(1, "sysctl name %d %zu %d", i, j, errno);
#ifdef __APPLE__
	}
#endif

	if (Nflag) {
		printf("%s", name);
		return (0);
	}

	if (eflag)
		sep = "=";
	else
		sep = ": ";

	if (dflag) {	/* just print description */
		qoid[1] = 5;
		j = sizeof(buf);
		i = sysctl(qoid, nlen + 2, buf, &j, 0, 0);
		if (!nflag)
			printf("%s%s", name, sep);
		printf("%s", buf);
		return (0);
	}
	/* find an estimate of how much we need for this var */
	j = 0;
	i = sysctl(oid, nlen, 0, &j, 0, 0);
	j += j; /* we want to be sure :-) */

	val = oval = malloc(j + 1);
	if (val == NULL) {
		warnx("malloc failed");
		return (1);
	}
	len = j;
	i = sysctl(oid, nlen, val, &len, 0, 0);
	if (i || !len) {
		free(oval);
		return (1);
	}

	if (bflag) {
		fwrite(val, 1, len, stdout);
		free(oval);
		return (0);
	}
	val[len] = '\0';
	p = val;
	ctltype = (kind & CTLTYPE);
	sign = ctl_sign[ctltype];
	intlen = ctl_size[ctltype];

	switch (ctltype) {
	case CTLTYPE_STRING:
		if (!nflag)
			printf("%s%s", name, sep);
		printf("%.*s", (int)len, p);
		free(oval);
		return (0);

	case CTLTYPE_INT:
	case CTLTYPE_UINT:
	case CTLTYPE_LONG:
	case CTLTYPE_ULONG:
	case CTLTYPE_S64:
	case CTLTYPE_U64:
		if (!nflag)
			printf("%s%s", name, sep);
		hexlen = (int)(2 + (intlen * CHAR_BIT + 3) / 4);
		sep1 = "";
		while (len >= intlen) {
			switch (kind & CTLTYPE) {
			case CTLTYPE_INT:
			case CTLTYPE_UINT:
				umv = *(u_int *)(void *)p;
				mv = *(int *)(void *)p;
				break;
			case CTLTYPE_LONG:
			case CTLTYPE_ULONG:
				umv = *(u_long *)(void *)p;
				mv = *(long *)(void *)p;
				break;
			case CTLTYPE_S64:
			case CTLTYPE_U64:
				umv = *(uint64_t *)(void *)p;
				mv = *(int64_t *)(void *)p;
				break;
			}
			fputs(sep1, stdout);
			if (xflag)
				printf("%#0*jx", hexlen, umv);
			else if (!sign)
				printf(hflag ? "%'ju" : "%ju", umv);
			else if (fmt[1] == 'K') {
				if (mv < 0)
					printf("%jd", mv);
				else
					printf("%.1fC", (mv - 2732.0) / 10);
			} else
				printf(hflag ? "%'jd" : "%jd", mv);
			sep1 = " ";
			len -= intlen;
			p += intlen;
		}
		free(oval);
		return (0);

	case CTLTYPE_OPAQUE:
		i = 0;
		if (strcmp(fmt, "S,clockinfo") == 0)
			func = S_clockinfo;
		else if (strcmp(fmt, "S,timeval") == 0)
			func = S_timeval;
		else if (strcmp(fmt, "S,loadavg") == 0)
			func = S_loadavg;
#ifdef __APPLE__
		else if (!strcmp(fmt, "S,xsw_usage"))
			func = S_xswusage;
		else if (!strcmp(fmt, "T,dev_t"))
			func = T_dev_t;
		else if (!strcmp(fmt, "Q"))
			func = S_quads;
#else // !__APPLE__
		else if (strcmp(fmt, "S,vmtotal") == 0)
			func = S_vmtotal;
#endif // !__APPLE__
		else
			func = NULL;
		if (func) {
			if (!nflag)
				printf("%s%s", name, sep);
			i = (*func)((int)len, p);
			free(oval);
			return (i);
		}
		/* FALLTHROUGH */
	default:
		if (!oflag && !xflag) {
			free(oval);
			return (1);
		}
		if (!nflag)
			printf("%s%s", name, sep);
		printf("Format:%s Length:%zu Dump:0x", fmt, len);
		while (len-- && (xflag || p < val + 16))
			printf("%02x", *p++);
		if (!xflag && len > 16)
			printf("...");
		free(oval);
		return (0);
	}
	return (1);
}

#ifdef __APPLE__
// Support for CTL_USER
static void
sysctl_all_user(int *oid, int len)
{
	int i, j;
	if (len > 1 || (len == 1 && oid[0] != CTL_USER)) {
		return;
	}
	for (i = 0; i < user_names_count; ++i) {
		int oid[2] = { CTL_USER, i };
		j = show_var(oid, 2, 0);
		if (!j && !bflag) {
			putchar('\n');
		}
	}
}
#endif

static int
sysctl_all(int *oid, int len)
{
	int name1[22], name2[22];
	int i, j;
	size_t l1, l2;

#ifdef __APPLE__
	sysctl_all_user(oid, len);
#endif

	name1[0] = 0;
	name1[1] = 2;
	l1 = 2;
	if (len) {
		memcpy(name1+2, oid, len * sizeof(int));
		l1 += len;
	} else {
		name1[2] = 1;
		l1++;
	}
	for (;;) {
		l2 = sizeof(name2);
		j = sysctl(name1, (u_int)l1, name2, &l2, 0, 0);
		if (j < 0) {
			if (errno == ENOENT)
				return (0);
			else
				err(1, "sysctl(getnext) %d %zu", j, l2);
		}

		l2 /= sizeof(int);

		if (len < 0 || l2 < (unsigned int)len)
			return (0);

		for (i = 0; i < len; i++)
			if (name2[i] != oid[i])
				return (0);

#ifdef __APPLE__
		i = show_var(name2, (u_int)l2, 0);
#else
		i = show_var(name2, (u_int)l2);
#endif
		if (!i && !bflag)
			putchar('\n');

		memcpy(name1+2, name2, l2 * sizeof(int));
		l1 = 2 + l2;
	}
}
