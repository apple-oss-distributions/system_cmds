/*-
 * Copyright (c) 2002 Tim J. Robbins.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

/*
 * newgrp -- change to a new group
 */

#include <sys/cdefs.h>
__FBSDID("$FreeBSD: src/usr.bin/newgrp/newgrp.c,v 1.5 2009/12/13 03:14:06 delphij Exp $");

#include <sys/types.h>

#include <err.h>
#include <errno.h>
#include <grp.h>
#include <libgen.h>
#include <limits.h>
#ifndef __APPLE__
#include <login_cap.h>
#endif /* !__APPLE__ */
#ifdef __APPLE__
#include <membership.h>
#endif /* __APPLE__ */
#include <pwd.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#ifdef __APPLE__
#include <paths.h>
#endif /* __APPLE__ */
static void	 addgroup(const char *grpname);
static void	 doshell(void);
static int	 inarray(gid_t, const gid_t[], int);
static void	 loginshell(void);
static void	 restoregrps(void);
static void	 usage(void);

static struct passwd *pwd;
static uid_t euid;

extern char **environ;

/* Manipulate effective user ID. */
#define PRIV_START do {				\
		if (seteuid(euid) < 0)		\
			err(1, "seteuid");	\
	} while (0)
#define PRIV_END do {				\
		if (seteuid(getuid()) < 0)	\
			err(1, "seteuid");	\
	} while (0)

int
main(int argc, char *argv[])
{
	int ch, login;

	euid = geteuid();
	if (seteuid(getuid()) < 0)
		err(1, "seteuid");

	if ((pwd = getpwuid(getuid())) == NULL)
		errx(1, "unknown user");

	login = 0;
	while ((ch = getopt(argc, argv, "-l")) != -1) {
		switch (ch) {
		case '-':		/* Obsolescent */
		case 'l':
			login = 1;
			break;
		default:
			usage();
		}
	}
	argc -= optind;
	argv += optind;

	switch (argc) {
	case 0:
		restoregrps();
		break;
	case 1:
		addgroup(*argv);
		break;
	default:
		usage();
	}

	if (seteuid(euid) < 0)
		err(1, "seteuid");
	if (setuid(getuid()) < 0)
		err(1, "setuid");

	if (login)
		loginshell();
	else
		doshell();

	/*NOTREACHED*/
	exit(1);
}

static void
usage(void)
{

	fprintf(stderr, "usage: newgrp [-l] [group]\n");
	exit(1);
}

static void
restoregrps(void)
{
	int initres, setres;

	PRIV_START;
	initres = initgroups(pwd->pw_name, pwd->pw_gid);
	setres = setgid(pwd->pw_gid);
	PRIV_END;

	if (initres < 0)
		warn("initgroups");
	if (setres < 0)
		warn("setgid");
}

static void
addgroup(const char *grpname)
{
	gid_t *grps;
	long lgid, ngrps_max;
	int dbmember, i, ngrps;
	gid_t egid;
	struct group *grp;
	char *ep, *pass;
	char **p;
	char *grp_passwd;
#ifdef __APPLE__
	uuid_t user_uuid;
	uuid_t group_uuid;
	int status;
#endif

	egid = getegid();

	/* Try it as a group name, then a group id. */
	if ((grp = getgrnam(grpname)) == NULL)
		if ((lgid = strtol(grpname, &ep, 10)) <= 0 || *ep != '\0' ||
		    (grp = getgrgid((gid_t)lgid)) == NULL ) {
			warnx("%s: bad group name", grpname);
			return;
		}

#ifdef __APPLE__
	status = mbr_uid_to_uuid(pwd->pw_uid, user_uuid);
	if (status)
		errc(1, status, "mbr_uid_to_uuid");

	status = mbr_gid_to_uuid(grp->gr_gid, group_uuid);
	if (status)
		errc(1, status, "mbr_gid_to_uuid");

	status = mbr_check_membership(user_uuid, group_uuid, &dbmember);
	if (status)
		errc(1, status, "mbr_check_membership");
#else
	/*
	 * If the user is not a member of the requested group and the group
	 * has a password, prompt and check it.
	 */
	dbmember = 0;
	if (pwd->pw_gid == grp->gr_gid)
		dbmember = 1;
	for (p = grp->gr_mem; *p != NULL; p++)
		if (strcmp(*p, pwd->pw_name) == 0) {
			dbmember = 1;
			break;
		}
#endif

	grp_passwd = grp->gr_passwd;
	if ((grp_passwd == NULL) || (grp_passwd[0] == '\0'))
		grp_passwd = "*";
	if (!dbmember && getuid() != 0) {
		pass = getpass("Password:");
		if (pass == NULL ||
		    strcmp(grp_passwd, crypt(pass, grp_passwd)) != 0) {
			fprintf(stderr, "Sorry\n");
			return;
		}
	}

	ngrps_max = sysconf(_SC_NGROUPS_MAX) + 1;
	if ((grps = malloc(sizeof(gid_t) * ngrps_max)) == NULL)
		err(1, "malloc");
	if ((ngrps = getgroups(ngrps_max, (gid_t *)grps)) < 0) {
		warn("getgroups");
		goto end;
	}

	/* Remove requested gid from supp. list if it exists. */
	if (grp->gr_gid != egid && inarray(grp->gr_gid, grps, ngrps)) {
		for (i = 0; i < ngrps; i++)
			if (grps[i] == grp->gr_gid)
				break;
		ngrps--;
		memmove(&grps[i], &grps[i + 1], (ngrps - i) * sizeof(gid_t));
		PRIV_START;
		if (setgroups(ngrps, (const gid_t *)grps) < 0) {
			PRIV_END;
			warn("setgroups");
			goto end;
		}
		PRIV_END;
	}

	PRIV_START;
	if (setgid(grp->gr_gid)) {
		PRIV_END;
		warn("setgid");
		goto end;
	}
	PRIV_END;
	grps[0] = grp->gr_gid;

	/* Add old effective gid to supp. list if it does not exist. */
	if (egid != grp->gr_gid && !inarray(egid, grps, ngrps)) {
		if (ngrps + 1 >= ngrps_max)
			warnx("too many groups");
		else {
			grps[ngrps++] = egid;
			PRIV_START;
			if (setgroups(ngrps, (const gid_t *)grps)) {
				PRIV_END;
				warn("setgroups");
				goto end;
			}
			PRIV_END;
		}
	}

end:
	free(grps);
}

static int
inarray(gid_t gid, const gid_t grps[], int ngrps)
{
	int i;

	for (i = 0; i < ngrps; i++)
		if (grps[i] == gid)
			return (1);
	return (0);
}

/*
 * Set the environment to what would be expected if the user logged in
 * again; this performs the same steps as su(1)'s -l option.
 */
static void
loginshell(void)
{
	char *args[2], **cleanenv, *term, *ticket;
	const char *shell;
	char *prog, progbuf[PATH_MAX];
#ifndef __APPLE__
	login_cap_t *lc;
#endif /* !__APPLE__ */
	shell = pwd->pw_shell;
	if (*shell == '\0')
		shell = _PATH_BSHELL;
	if (chdir(pwd->pw_dir) < 0) {
		warn("%s", pwd->pw_dir);
		chdir("/");
	}

	term = getenv("TERM");
	ticket = getenv("KRBTKFILE");

	if ((cleanenv = calloc(20, sizeof(char *))) == NULL)
		err(1, "calloc");
	*cleanenv = NULL;
	environ = cleanenv;
#ifndef __APPLE__
	lc = login_getpwclass(pwd);
	setusercontext(lc, pwd, pwd->pw_uid,
	    LOGIN_SETPATH|LOGIN_SETUMASK|LOGIN_SETENV);
	login_close(lc);
#endif /* !__APPLE__ */
	setenv("USER", pwd->pw_name, 1);
	setenv("SHELL", shell, 1);
	setenv("HOME", pwd->pw_dir, 1);
	if (term != NULL)
		setenv("TERM", term, 1);
	if (ticket != NULL)
		setenv("KRBTKFILE", ticket, 1);

	strlcpy(progbuf, shell, sizeof(progbuf));
	prog = basename(progbuf);

	if (asprintf(args, "-%s", prog) < 0)
		err(1, "asprintf");
	args[1] = NULL;

	execv(shell, args);
	err(1, "%s", shell);
}

static void
doshell(void)
{
	const char *shell;
	char *prog, progbuf[PATH_MAX];

	shell = pwd->pw_shell;
	if (*shell == '\0')
		shell = _PATH_BSHELL;

	strlcpy(progbuf, shell, sizeof(progbuf));
	prog = basename(progbuf);

	execl(shell, prog, (char *)NULL);
	err(1, "%s", shell);
}
