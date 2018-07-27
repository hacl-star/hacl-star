# hacl build container

# Define here what FStar base container image hacl build should use.
# By default it always look for the latest FStar container available
# In case you would like to reference a specific commit,
# replace latest with the commit id from github using 12 characters.
# i.e.: FROM fstar:cbac9b43ab46
FROM fstar:latest

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

RUN mkdir ${MYHOME}/FStar/mitls-fstar
COPY --chown=everest / ${MYHOME}/FStar/mitls-fstar/
WORKDIR ${MYHOME}/FStar/mitls-fstar

COPY --chown=everest build_miTLS.sh ${MYHOME}/FStar/mitls-fstar/build_miTLS.sh
RUN chmod +x build_miTLS.sh
COPY --chown=everest build.sh ${MYHOME}/FStar/mitls-fstar/build.sh
RUN chmod +x build.sh

RUN echo $(date -u '+%Y-%m-%d %H:%M:%S') >> ${BUILDLOGFILE}
RUN ./build.sh ${TARGET} ${BUILDLOGFILE} ${MAXTHREADS} || true
RUN echo $(date -u '+%Y-%m-%d %H:%M:%S') >> ${BUILDLOGFILE}

# Generate query-stats.
# List the hints that fail to replay.
RUN bash -c "../.scripts/query-stats.py -f ${BUILDLOGFILE} -F html -o log_no_replay.html -n all '--filter=fstar_usedhints=+' '--filter=fstar_tag=-' -g"

# Worst offenders (longest times)
RUN bash -c "../.scripts/query-stats.py -f ${BUILDLOGFILE} -F html -o log_worst.html -c -g -n 10"

