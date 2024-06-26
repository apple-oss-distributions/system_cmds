# Copyright (c) 2022 Yoshihiro Ota <ota@j.email.ne.jp>
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions
# are met:
# 1. Redistributions of source code must retain the above copyright
#    notice, this list of conditions and the following disclaimer.
# 2. Redistributions in binary form must reproduce the above copyright
#    notice, this list of conditions and the following disclaimer in the
#    documentation and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
# ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
# ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
# OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
# HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
# LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
# OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
# SUCH DAMAGE.

sysctl_name="kern.ostype"
#ifdef __APPLE__
sysctl_value="Darwin"
#else
#sysctl_value="FreeBSD"
#endif
sysctl_type="string"
sysctl_description="Operating system type"

atf_test_case sysctl_by_name
sysctl_by_name_head()
{
	atf_set "descr" "Verify name without any arguments"
}
sysctl_by_name_body()
{
	atf_check -o "inline:${sysctl_name}: ${sysctl_value}\n" sysctl ${sysctl_name}
}


atf_test_case sysctl_nflag
sysctl_nflag_head()
{
	atf_set "descr" "Verify -n argument"
}
sysctl_nflag_body()
{
	atf_check -o "inline:${sysctl_value}\n" sysctl -n ${sysctl_name}
}


atf_test_case sysctl_eflag
sysctl_eflag_head()
{
	atf_set "descr" "Verify -e argument"
}
sysctl_eflag_body()
{
	atf_check -o "inline:${sysctl_name}=${sysctl_value}\n" sysctl -e ${sysctl_name}
}


atf_test_case sysctl_tflag
sysctl_tflag_head()
{
	atf_set "descr" "Verify -t argument"
}
sysctl_tflag_body()
{
	atf_check -o "inline:${sysctl_name}: ${sysctl_type}\n" sysctl -t ${sysctl_name}
}


atf_test_case sysctl_dflag
sysctl_dflag_head()
{
	atf_set "descr" "Verify -d argument"
}
sysctl_dflag_body()
{
	atf_check -o "inline:${sysctl_name}: ${sysctl_description}\n" sysctl -d ${sysctl_name}
}


atf_test_case sysctl_tflag_dflag
sysctl_tflag_dflag_head()
{
	atf_set "descr" "Verify -t -d arguments"
}
sysctl_tflag_dflag_body()
{
	atf_check -o "inline:${sysctl_name}: ${sysctl_type}: ${sysctl_description}\n" sysctl -t -d ${sysctl_name}
	atf_check -o "inline:${sysctl_name}: ${sysctl_type}: ${sysctl_description}\n" sysctl -d -t ${sysctl_name}
}


atf_test_case sysctl_nflag_tflag_dflag
sysctl_nflag_tflag_dflag_head()
{
	atf_set "descr" "Verify -n -t -d arguments"
}
sysctl_nflag_tflag_dflag_body()
{
	atf_check -o "inline:${sysctl_type}: ${sysctl_description}\n" sysctl -n -t -d ${sysctl_name}
}

#ifdef __APPLE__
atf_test_case sysctl_dflt
sysctl_dflt_head()
{
	atf_set "descr" "Verify the default behavior with no flags, just an OID"
}
sysctl_dflt_body()
{
	atf_check -o match:"kern.maxfiles: [0-9]+$" sysctl kern.maxfiles
}

atf_test_case sysctl_write
sysctl_write_head()
{
	atf_set "descr" "Verify that sysctl(8) can write to an OID"
	atf_set "require.user" "root"
}
sysctl_write_body()
{
	maxfiles=$(sysctl -n kern.maxfiles)
	newmax=$((maxfiles + 1))

	# We shouldn't really have anything running concurrently that can change
	# this out from underneath us.  We just need to make sure that no other
	# sysctl(8) tests require or record a specific value from kern.maxfiles.
	atf_check -o inline:"kern.maxfiles: ${maxfiles} -> ${newmax}\n" \
	    sysctl kern.maxfiles=${newmax}
	atf_check -o inline:"${newmax}\n" sysctl -n kern.maxfiles
}
#endif

atf_init_test_cases()
{
	atf_add_test_case sysctl_by_name
	atf_add_test_case sysctl_nflag
	atf_add_test_case sysctl_eflag
	atf_add_test_case sysctl_tflag
#ifdef __APPLE__
	atf_add_test_case sysctl_dflt
	atf_add_test_case sysctl_write
#else
#	atf_add_test_case sysctl_dflag
#	atf_add_test_case sysctl_tflag_dflag
#	atf_add_test_case sysctl_nflag_tflag_dflag
#endif
}
