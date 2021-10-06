/* File created by Chris Youngworth, Apple Computer 2/11/99 */


#define mig_external

#include <mach/port.h>
#include <mach/mach_error.h>
#include <mach/mach_traps.h>
#include <mach/mach.h>
#ifndef MACH_BSD
#define MACH_BSD
#endif
#include <mach/bootstrap.h>
#include <mach/mach_syscalls.h>
#include <mach/mig_errors.h>
#include <sys/param.h>
#include <sys/mount.h>
#include <sys/file.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/sysctl.h>
#include <sys/gmon.h>
#include <errno.h>
#include <kvm.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <nlist.h>
#include <ctype.h>
#include <unistd.h> 
#include <paths.h>

#include <default_pager/default_pager_types.h>
#include <default_pager_alerts_server.h>
#include <backing_store_alerts.h>
#include <backing_store_triggers_server.h>


/*
 * HI_WATER_DEFAULT set to this funny value to 
 * match the size that the low space application
 * is asking for... need to keep MINIMUM_SIZE
 * above this value.
 */
#define HI_WATER_DEFAULT 40000000
#define MINIMUM_SIZE (1024 * 1024 * 64)
#define MAXIMUM_SIZE  (1024 * 1024 * 1024)

#define MAX_LIMITS 8


struct limit {
        unsigned int size;
        unsigned int low_water;
} limits[MAX_LIMITS];


int	debug = 0;
int     max_valid  = 0;
int	file_count = 0;
unsigned int	hi_water;
unsigned int	local_hi_water;
int	priority = 0;
int	options  = 0;
char	fileroot[512];


/* global parameters for application notification option */
mach_port_t	trigger_port = MACH_PORT_NULL;
mach_port_t	notify_port = MACH_PORT_NULL;
unsigned int	notify_high = 0;
unsigned int	bs_recovery;

/*
void	setprof __P((struct kvmvars *kvp, int state));
void	dumpstate __P((struct kvmvars *kvp));
void	reset __P((struct kvmvars *kvp));
*/



mach_msg_return_t
server_alert_loop(
    mach_msg_size_t max_size,
    mach_port_t rcv_name,
    mach_msg_options_t options)
{
    mig_reply_error_t *bufRequest = 0, *bufReply = 0;
    register mach_msg_return_t mr;
    register kern_return_t kr;

    if ((kr = vm_allocate(mach_task_self(),
                     (vm_address_t *)&bufRequest,
                     max_size + MAX_TRAILER_SIZE,
                     TRUE)) != KERN_SUCCESS)
      return kr;
    if ((kr = vm_protect(mach_task_self(),
                     (vm_address_t)bufRequest,
                     max_size + MAX_TRAILER_SIZE,
		     FALSE, VM_PROT_ALL)) != KERN_SUCCESS)
      return kr;
    mlock(bufRequest, max_size + MAX_TRAILER_SIZE);
    if ((kr = vm_allocate(mach_task_self(),
                     (vm_address_t *)&bufReply,
                     max_size + MAX_TRAILER_SIZE,
                     TRUE)) != KERN_SUCCESS)
      return kr;
    if ((kr = vm_protect(mach_task_self(),
                     (vm_address_t)bufReply,
                     max_size + MAX_TRAILER_SIZE,
		     FALSE, VM_PROT_ALL)) != KERN_SUCCESS)
      return kr;
    mlock(bufReply, max_size + MAX_TRAILER_SIZE);
    while(TRUE) {
       mr = mach_msg_overwrite_trap(&bufRequest->Head, MACH_RCV_MSG|options,
                                 0, max_size, rcv_name,
                                 MACH_MSG_TIMEOUT_NONE, MACH_PORT_NULL,
                                 (mach_msg_header_t *) 0, 0);
        if (mr == MACH_MSG_SUCCESS) {
           /* we have a request message */

           if(!(default_pager_alerts_server(
				&bufRequest->Head, &bufReply->Head)))
		backing_store_triggers_server(
				&bufRequest->Head, &bufReply->Head);

           if (!(bufReply->Head.msgh_bits & MACH_MSGH_BITS_COMPLEX) &&
               bufReply->RetCode != KERN_SUCCESS) {
               if (bufReply->RetCode == MIG_NO_REPLY)
                /*
                 * This return code is a little tricky--
                 * it appears that the demux routine found an
                 * error of some sort, but since that error
                 * would not normally get returned either to
                 * the local user or the remote one, we pretend it's
                 * ok.
                 */

               bufRequest->Head.msgh_remote_port = MACH_PORT_NULL;
               mach_msg_destroy(&bufRequest->Head);
	       continue;
           }

           if (bufReply->Head.msgh_remote_port == MACH_PORT_NULL) {
              /* no reply port, so destroy the reply */
              if (bufReply->Head.msgh_bits & MACH_MSGH_BITS_COMPLEX)
                  mach_msg_destroy(&bufReply->Head);
	   } else {
		break;
	   }
	} else {
	   break;
	}   
    } 

    (void)vm_deallocate(mach_task_self(),
                    (vm_address_t) bufRequest,
                    max_size + MAX_TRAILER_SIZE);
    (void)vm_deallocate(mach_task_self(),
                    (vm_address_t) bufReply,
                    max_size + MAX_TRAILER_SIZE);
    return KERN_FAILURE;

}       


kern_return_t
backing_store_triggers(dynamic_pager, hi_wat, flags, port)
 		mach_port_t	dynamic_pager;
		int		hi_wat;
		int		flags;
		mach_port_t 	port;
{
        int cur_limits;
	
	if (file_count > max_valid)
	        cur_limits = max_valid;
	else
	        cur_limits = file_count;

	if((hi_wat + limits[cur_limits].size) > limits[cur_limits].low_water) 
		return KERN_FAILURE; /* let ipc system clean up port */

	/* If there was a previous registration, throw it away */
	if (notify_port != MACH_PORT_NULL) {
		mach_port_deallocate(mach_task_self(), notify_port);
		notify_port = MACH_PORT_NULL;
	}

	notify_port = port;
	notify_high = hi_wat;
	if(hi_water < notify_high) {
		local_hi_water = notify_high;
	} else {
		local_hi_water = hi_water;
	}
	if(notify_high > hi_water) {
		default_pager_space_alert(trigger_port, HI_WAT_ALERT);
	}
	return KERN_SUCCESS;
}


kern_return_t
default_pager_space_alert(alert_port, flags)
	mach_port_t	alert_port;
	int	flags;
{
	char subfile[512];
	FILE *file_ptr;
	off_t	filesize;
	int	error;
	kern_return_t	ret;
        int cur_limits;
	unsigned int cur_size;
	unsigned int notifications;

	
	if(flags & HI_WAT_ALERT) {

		file_count++;

		if (file_count > max_valid)
		        cur_limits = max_valid;
		else
		        cur_limits = file_count;

		cur_size = limits[cur_limits].size;
		filesize = cur_size;

		/*
		 * because the LO_WAT threshold changes relative to
		 * the size of the swap file we're creating
		 * we need to reset the LO_WAT_ALERT threshold each
		 * time we create a new swap file
		 */
		if (limits[cur_limits].low_water)
		        notifications = HI_WAT_ALERT | LO_WAT_ALERT;
		else
		        notifications = HI_WAT_ALERT;

		sprintf(subfile, "%s%d", fileroot, file_count);
		file_ptr = fopen(subfile, "w+");
		fchmod(fileno(file_ptr), (mode_t)01600);
		error = fcntl(fileno(file_ptr), F_SETSIZE, &filesize);
		if(error) {
			error = ftruncate(fileno(file_ptr), filesize);
		}
		fclose(file_ptr);

		if(error == -1) {
			unlink(subfile);
			file_count--;

			if (file_count > max_valid)
			        cur_limits = max_valid;
			else
			        cur_limits = file_count;

			if (limits[cur_limits].low_water)
			        notifications = HI_WAT_ALERT | LO_WAT_ALERT;
			else
			        notifications = HI_WAT_ALERT;

			local_hi_water = local_hi_water>>2;
			if(notify_high >= (local_hi_water)) {
				if(notify_port != MACH_PORT_NULL) {
					/* notify monitoring app of */
					/* backing store shortage  */
					backing_store_alert(notify_port,
								HI_WAT_ALERT);
					mach_port_deallocate(mach_task_self(), 
								notify_port);
					notify_port = MACH_PORT_NULL;
					notify_high = 0;
				}
			}
			macx_triggers(local_hi_water, limits[cur_limits].low_water, notifications, alert_port);
		} else {
			if(hi_water < notify_high) {
				if(local_hi_water < notify_high) {
				   bs_recovery = notify_high - local_hi_water;
				}
				local_hi_water = notify_high;
			} else {
				if(local_hi_water < hi_water) {
				   bs_recovery = hi_water - local_hi_water;
				}
				local_hi_water = hi_water;
			}
			ret = macx_swapon(subfile, flags, cur_size, priority);

			if(ret) {
				unlink(subfile);
				file_count--;

				if (file_count > max_valid)
				        cur_limits = max_valid;
				else
				        cur_limits = file_count;

				if (limits[cur_limits].low_water)
				        notifications = HI_WAT_ALERT | LO_WAT_ALERT;
				else
				        notifications = HI_WAT_ALERT;

				local_hi_water = local_hi_water>>2;
				if(notify_high >= (local_hi_water)) {
					if(notify_port != MACH_PORT_NULL) {
						/* notify monitoring app of */
						/* backing store shortage  */
						backing_store_alert(
							notify_port,
							HI_WAT_ALERT);
						mach_port_deallocate(
							mach_task_self(), 
							notify_port);
						notify_port = MACH_PORT_NULL;
						notify_high = 0;
					}
				}
				macx_triggers(local_hi_water, limits[cur_limits].low_water, notifications, alert_port);
			} else if(bs_recovery <= cur_size) {
				if((bs_recovery != 0) && (notify_port)) {
					backing_store_alert(notify_port,
								LO_WAT_ALERT);
					mach_port_deallocate(mach_task_self(), 
								notify_port);
					notify_port = MACH_PORT_NULL;
					notify_high = 0;
					bs_recovery = 0;
				}
			} else 
				bs_recovery = bs_recovery-cur_size;
		}
		macx_triggers(local_hi_water, limits[cur_limits].low_water, notifications, alert_port);
	}
	if(flags & LO_WAT_ALERT) {
		sprintf(subfile, "%s%d", fileroot, file_count);
		if(hi_water < notify_high) {
			local_hi_water = notify_high;
		} else {
			local_hi_water = hi_water;
		}
		if((bs_recovery != 0) && (notify_port != MACH_PORT_NULL)) {
			backing_store_alert(notify_port, LO_WAT_ALERT);
			mach_port_deallocate(mach_task_self(), notify_port);
			notify_port = MACH_PORT_NULL;
			notify_high = 0;
			bs_recovery = 0;
		}
		if((error = macx_swapoff(subfile, flags)) == 0) {

			unlink(subfile);
			file_count--;

			if (file_count > max_valid)
			        cur_limits = max_valid;
			else
			        cur_limits = file_count;
		} else {
			if (file_count > max_valid)
			        cur_limits = max_valid;
			else
			        cur_limits = file_count;
		}
		/*
		 * only need to reset the LO_WAT_ALERT... the HI_WAT size is fixed,
		 * it doesn't change even if the swap file size shrinks or grows
		 */
		macx_triggers(local_hi_water, limits[cur_limits].low_water, LO_WAT_ALERT, alert_port);
	}
	return KERN_SUCCESS;
}

void
wait_on_paging_trigger(trigger_port)
	mach_port_t	trigger_port;
{
	kern_return_t	result;
	result = server_alert_loop(4096, trigger_port, MACH_MSG_OPTION_NONE);
	if (result != KERN_SUCCESS) {
	     fprintf(stderr, "dynamic_pager: default pager alert failed\n");
	     exit(1);
	}
	exit(0);
}

void
paging_setup(flags, size, priority, low, high)
	int	flags;
	int	size;
	int	priority;
	int	low;
	int	high;
{
	off_t		filesize = size;
	char 		subfile[512];
	FILE 		*file_ptr;
	int		error;

	file_count = 0;
	sprintf(subfile, "%s%d", fileroot, file_count);
	file_ptr = fopen(subfile, "w+");
	fchmod(fileno(file_ptr), (mode_t)01600);
	error = fcntl(fileno(file_ptr), F_SETSIZE, &filesize);
	if(error) {
	error = ftruncate(fileno(file_ptr), filesize);
	}
	fclose(file_ptr);
        
	macx_swapon(subfile, flags, size, priority);

	if(hi_water) {
		mach_msg_type_name_t    poly;

		daemon(0,0);

		if (mach_port_allocate(mach_task_self(), 
				MACH_PORT_RIGHT_RECEIVE, 
				&trigger_port) != KERN_SUCCESS)  {
			fprintf(stderr,"allocation of trigger port failed\n");
			exit(1);
		}
		/* create a send right on our local port */
		mach_port_extract_right(mach_task_self(), trigger_port,
			MACH_MSG_TYPE_MAKE_SEND, &trigger_port, &poly);
		macx_triggers(high, low, HI_WAT_ALERT, trigger_port);

		if(low) {
			macx_triggers(high, low, LO_WAT_ALERT, trigger_port);
		}
		/* register control port for applications wishing to */
		/* get backing store notifications or change dynamic */
		/* pager settings. */
		set_dp_control_port(mach_host_self(), trigger_port);
		wait_on_paging_trigger(trigger_port); 
	}
	exit(0);
}
int
main(int argc, char **argv)
{
	extern char *optarg;
	extern int optind;
	char default_filename[] = "/private/var/vm/swapfile";
	int ch;
	int variable_sized = 1;

	seteuid(getuid());
	strcpy(fileroot, default_filename);

	limits[0].size = 20000000;
	limits[0].low_water = 0;

	hi_water = 0;
	local_hi_water = 0;


	while ((ch = getopt(argc, argv, "F:L:H:S:P:O:")) != EOF) {
		switch((char)ch) {

		case 'F':
			strncpy(fileroot, optarg, 500);
			break;

		case 'L':
		        variable_sized = 0;
			limits[0].low_water = atoi(optarg);
			break;
		case 'H':
		        variable_sized = 0;
			hi_water = atoi(optarg);
			break;
		case 'S':
		        variable_sized = 0;
			limits[0].size = atoi(optarg);
			break;
		case 'P':
			priority = atoi(optarg);
			break;

		default:
			(void)fprintf(stderr,
			    "usage: dynamic_pager [-F filename] [-L low water alert trigger] [-H high water alert trigger] [-S file size] [-P priority]\n");
			exit(1);
		}
	}

	if (variable_sized) {
	        static char tmp[1024];
		struct statfs sfs;
		char *q;
		int  i;
		int  mib[4];
		size_t len;
		unsigned int size;
		u_int64_t  memsize;
		u_int64_t  fs_limit;

		/*
		 * if we get here, then none of the following options were specified... -L, H, or -S
		 * drop into a new mode that scales the size of the swap file based on how much free
		 * space is left on the volume being used for swap and the amount of physical ram 
		 * installed on the system...
		 * basically, we'll pick a maximum size that doesn't exceed the following limits...
		 *   1/4 the remaining free space of the swap volume 
		 *   the size of phsyical ram
		 *   MAXIMUM_SIZE - currently set to 1 Gbyte... 
		 * once we have the maximum, we'll create a list of sizes and low_water limits
		 * we'll start with 2 files of MINIMUM_SIZE - currently 64 Mbytes...
		 * subsequent entries will double in size up to the calculated maximum... the low_water
		 * limit will be the sum of the current file size and the previous file size for each entry...
		 * as we add or delete files, we'll use the current file_count as an index into this 
		 * table... if it's beyond the table size, we'll use the last entry
		 * the table entry will determine the size of the file to be created and the new low_water mark...
		 * the high_water mark is set to HI_WATER_DEFAULT which  must be smaller than MINIMUM_SIZE...
		 * currently it is set to 40,000,000 to match the size being requested by the application 
		 * monitoring low space conditions... having it set to the same size keeps us from creating
		 * an additional swap file when it really isn't necessary
		 */

		/*
		 * get rid of the filename at the end of the swap file specification
		 * we only want the portion of the pathname that should already exist
		 */
	        strcpy(tmp, fileroot);
		if (q = strrchr(tmp, '/'))
		        *q = 0;

	        if (statfs(tmp, &sfs) != -1) {
		        /*
			 * limit the maximum size of a swap file to 1/4 the free
			 * space available on the filesystem where the swap files
			 * are to reside
			 */
		        fs_limit = ((u_int64_t)sfs.f_bfree * (u_int64_t)sfs.f_bsize) / 4;

		} else {
		        (void)fprintf(stderr, "usage: swap directory must exist\n"); 
			exit(1);
		}
		mib[0] = CTL_HW;
		mib[1] = HW_MEMSIZE;
		len = sizeof(u_int64_t);

		if (sysctl(mib, 2, &memsize, &len, NULL, 0) < 0) {
		        /*
			 * if the sysctl fails for some reason
			 * use the starting size as the default
			 */
		        memsize = MINIMUM_SIZE;
		}
		if (memsize > fs_limit)
		        /*
			 * clip based on filesystem space available
			 */
		        memsize = fs_limit;

		/*
		 * further limit the maximum size of a swap file
		 */
		if (memsize > MAXIMUM_SIZE)
		        memsize = MAXIMUM_SIZE;
		
		size = MINIMUM_SIZE;

		/*
		 * start small and work our way up to the maximum
		 * sized allowed... this way, we don't tie up too
		 * much disk space if we never do any real paging
		 */
		for (max_valid = 0, i = 0; i < MAX_LIMITS; i++) {
		        limits[i].size = size;

			if (i == 0)
			        limits[i].low_water = size * 2;
			else {
			        if ((limits[i - 1].size / 2) > HI_WATER_DEFAULT)
				        limits[i].low_water = size + (limits[i - 1].size / 2);
				else
				        limits[i].low_water = size + limits[i - 1].size;
			}
			if (size >= memsize)
			        break;
			
			if (i) {
			        /*
				 * make the first 2 files the same size
				 */
			        size = size * 2;
			}
			max_valid++;
		}
		if (max_valid >= MAX_LIMITS)
		        max_valid = MAX_LIMITS - 1;

		hi_water = HI_WATER_DEFAULT;
	}
	local_hi_water = hi_water;

	if((limits[0].low_water != 0) && (limits[0].low_water <= (limits[0].size + hi_water))) {
		(void)fprintf(stderr,  "usage: low water trigger must be larger than size + hi_water\n"); 
		exit(1);
	}
	argc -= optind;
	argv += optind;

	paging_setup(0, limits[0].size, priority, limits[0].low_water, hi_water);

	return (0);
}
