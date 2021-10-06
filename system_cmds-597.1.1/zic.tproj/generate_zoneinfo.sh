#!/bin/sh
set -e
set -x

printenv | sort

if [ $# -ne 5 ]; then
    echo "Usage: $0 SRCROOT OBJROOT BUILT_PRODUCTS_DIR SDKROOT PLATFORM_NAME" 1>&2
    exit 1
fi

SRCROOT="$1"
OBJROOT="$2"
BUILT_PRODUCTS_DIR="$3"
SDKROOT="$4"
PLATFORM_NAME="$5"

ZICHOST_SYMROOT="${BUILT_PRODUCTS_DIR}/zic_host-sym"
ZICHOST_DSTROOT="${BUILT_PRODUCTS_DIR}/zic_host-dst"
ZICHOST="${ZICHOST_DSTROOT}/zic_host"

LOCALTIME="US/Pacific"
POSIXRULES="US/Pacific"

# pacificnew is obsolete and was removed from ZONE_FILES
ZONE_FILES="africa antarctica asia australasia europe northamerica southamerica etcetera factory backward systemv solar87 solar88 solar89"
ZONEINFO="${BUILT_PRODUCTS_DIR}/zoneinfo"
DATFILES="${BUILT_PRODUCTS_DIR}/datfiles"
PRIVATEDIR="${BUILT_PRODUCTS_DIR}/private"

# ftp://elsie.nci.nih.gov/pub/tzdata*.tar.gz
# the tzdata*.tar.gz file is automatically unpacked and a version file created
# /usr/local/share/tz/tzdata*.tar.gz is installed by the TimeZoneData project
TARBALL=`ls ${SDKROOT}/usr/local/share/tz/tzdata* | sort | tail -n 1`
if [ -z "$TARBALL" ]; then
    echo "No tzdata file found in ${SDKROOT}/usr/local/share/tz" 1>&2
    exit 1
fi
DATVERS=`basename ${TARBALL} | sed -e 's,\..*,,' -e 's/^tzdata//'`
VERSIONFILE="${ZONEINFO}/+VERSION"

mkdir -p "${DATFILES}"
mkdir -p "${ZONEINFO}"
tar zxf "${TARBALL}" -C "${DATFILES}"
for tz in ${ZONE_FILES}; do
    if [ ${tz} = "northamerica" ]; then
        ARG="-p America/New_York"
    else
        ARG=""
    fi
    ${ZICHOST} ${ARG} -L /dev/null -d "${ZONEINFO}" \
        -y "${DATFILES}/yearistype.sh" "${DATFILES}/${tz}" || exit 1
done
if [ $? -ne 0 ]; then
    exit 1
fi

chmod -R og-w "${ZONEINFO}"
for f in "zone.tab" "iso3166.tab"; do
    install -m 0444 "${DATFILES}/$f" "${ZONEINFO}/$f" || exit 1
done
if [ $? -ne 0 ]; then
    exit 1
fi

if [ "${PLATFORM_NAME}" = "iphoneos" ]; then
    mkdir -p "${PRIVATEDIR}/var/db"
    mkdir -p -m a+rwx "${PRIVATEDIR}/var/db/timezone"

    # This link must precisely start with TZDIR followed by a slash. radar:13532660
    ln -hfs "/var/db/timezone/zoneinfo/${LOCALTIME}" "${PRIVATEDIR}/var/db/timezone/localtime"
else
    mkdir -p "${PRIVATEDIR}/etc"
    ln -hfs "/usr/share/zoneinfo/${LOCALTIME}" "${PRIVATEDIR}/etc/localtime"
fi

rm -f "${VERSIONFILE}"
echo ${DATVERS} > "${VERSIONFILE}"
chmod 444 "${VERSIONFILE}"
touch "${ZONEINFO}"
touch "${PRIVATEDIR}"

