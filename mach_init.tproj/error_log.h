/*
 * Copyright (c) 1999 Apple Computer, Inc. All rights reserved.
 *
 * @APPLE_LICENSE_HEADER_START@
 * 
 * "Portions Copyright (c) 1999 Apple Computer, Inc.  All Rights
 * Reserved.  This file contains Original Code and/or Modifications of
 * Original Code as defined in and that are subject to the Apple Public
 * Source License Version 1.0 (the 'License').  You may not use this file
 * except in compliance with the License.  Please obtain a copy of the
 * License at http://www.apple.com/publicsource and read it before using
 * this file.
 * 
 * The Original Code and all software distributed under the License are
 * distributed on an 'AS IS' basis, WITHOUT WARRANTY OF ANY KIND, EITHER
 * EXPRESS OR IMPLIED, AND APPLE HEREBY DISCLAIMS ALL SUCH WARRANTIES,
 * INCLUDING WITHOUT LIMITATION, ANY WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE OR NON-INFRINGEMENT.  Please see the
 * License for the specific language governing rights and limitations
 * under the License."
 * 
 * @APPLE_LICENSE_HEADER_END@
 */
/*
 * bootstrap -- fundamental service initiator and port server
 * Mike DeMoney, NeXT, Inc.
 * Copyright, 1990.  All rights reserved.
 *
 * error_log.h -- interface to logging routines
 */

#import <mach/mach.h>

extern void init_errlog(boolean_t);
extern void stop_errlog(void);
extern void close_errlog(void);
extern void debug(const char *format, ...);
extern void info(const char *format, ...);
extern void notice(const char *format, ...);
extern void error(const char *format, ...);
extern void kern_error(kern_return_t result, const char *format, ...);
extern void parse_error(const char *token_string, const char *format, ...);
extern void unix_error(const char *msg, ...);
extern void fatal(const char *msg, ...);
extern void kern_fatal(kern_return_t result, const char *msg, ...);
extern void unix_fatal(const char *msg, ...);

