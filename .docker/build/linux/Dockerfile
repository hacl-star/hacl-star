# hacl build container

# Define on fstar-version.json what FStar base container image
# hacl build should use.
# By default it always look for the latest FStar container available
# In case you would like to reference a specific commit,
# replace latest with the commit id from github using 12 characters.
# Latest can only be used with branch master,
# for any other branch please use the specific commit id on the config file.
ARG COMMITID
FROM fstar:${COMMITID}

ARG BUILDLOGFILE
ARG MAXTHREADS
ARG TARGET

RUN export FSTAR_HOME=${MYHOME}/FStar

# Do some cleanup
RUN rm -rf hacl-star
RUN rm -rf hacl-star-old
RUN rm -rf kremlin
RUN rm -rf hacl-star
RUN rm -rf mitls-fstar
RUN rm -rf vale

RUN rm -f build.sh
RUN rm -f build_fstar.sh
RUN rm -f buildlogfile.txt
RUN rm -f log_no_replay.html
RUN rm -f log_worst.html
RUN rm -f orange_status.txt
RUN rm -f result.txt
RUN rm -f status.txt
RUN rm -f commitinfofilename.json

RUN mkdir ${MYHOME}/FStar/hacl-star
COPY --chown=everest / ${MYHOME}/FStar/hacl-star/

# Hacl make calls git clean, which will delete buildlogfile.txt
# Because of that we will first output on the parent folder
WORKDIR ${MYHOME}/FStar

COPY --chown=everest build_hacl.sh ${MYHOME}/FStar/build_hacl.sh
RUN chmod +x build_hacl.sh
COPY --chown=everest build.sh ${MYHOME}/FStar/build.sh
RUN chmod +x build.sh

RUN echo $(date -u '+%Y-%m-%d %H:%M:%S') >> ${BUILDLOGFILE}
RUN ./build.sh ${TARGET} ${BUILDLOGFILE} ${MAXTHREADS} || true
RUN echo $(date -u '+%Y-%m-%d %H:%M:%S') >> ${BUILDLOGFILE}

# Generate query-stats.
# List the hints that fail to replay.
RUN bash -c ".scripts/query-stats.py -f ${BUILDLOGFILE} -F html -o log_no_replay.html -n all '--filter=fstar_usedhints=+' '--filter=fstar_tag=-' -g"

# Worst offenders (longest times)
RUN bash -c ".scripts/query-stats.py -f ${BUILDLOGFILE} -F html -o log_worst.html -c -g -n 10"

