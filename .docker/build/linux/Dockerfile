# hacl build container

# Define on fstar-version.json what FStar base container image
# hacl build should use.
# By default it always look for the latest FStar container available
# In case you would like to reference a specific commit,
# replace latest with the commit id from github using 12 characters.
# Latest can only be used with branch master,
# for any other branch please use the specific commit id on the config file.
ARG COMMITID
FROM fstar-linux:${COMMITID}

ARG BUILDLOGFILE
ARG MAXTHREADS
ARG TARGET
ARG BRANCHNAME
ARG COMMITID

RUN export FSTAR_HOME=${MYHOME}/FStar

WORKDIR ${MYHOME}/FStar

# Do some cleanup
RUN rm -rf hacl-star
RUN rm -rf hacl-star-old
RUN rm -rf kremlin
RUN rm -rf hacl-star
RUN rm -rf mitls-fstar
RUN rm -rf vale

RUN rm -f build.sh
RUN rm -f build_helper.sh
RUN rm -f buildlogfile.txt
RUN rm -f log_no_replay.html
RUN rm -f log_worst.html
RUN rm -f orange_status.txt
RUN rm -f result.txt
RUN rm -f status.txt
RUN rm -f commitinfofilename.json

RUN mkdir ${MYHOME}/FStar/hacl-star
COPY --chown=everest / ${MYHOME}/FStar/hacl-star/

# Do another cleanup
RUN rm ${MYHOME}/FStar/hacl-star/Dockerfile
RUN rm ${MYHOME}/FStar/hacl-star/build_helper.sh
RUN rm ${MYHOME}/FStar/hacl-star/build.sh
RUN rm ${MYHOME}/FStar/hacl-star/id_rsa
RUN rm ${MYHOME}/FStar/hacl-star/commitinfofilename.json

# ADD SSH KEY
RUN mkdir -p ${MYHOME}/.ssh
RUN chown everest ${MYHOME}/.ssh
RUN chmod 700 ${MYHOME}/.ssh
COPY --chown=everest id_rsa ${MYHOME}/.ssh/id_rsa
RUN chmod 600 ${MYHOME}/.ssh/id_rsa
RUN eval $(ssh-agent)

COPY --chown=everest build.sh ${MYHOME}/FStar/build.sh
RUN chmod +x build.sh
COPY --chown=everest build_helper.sh ${MYHOME}/FStar/build_helper.sh
RUN chmod +x build_helper.sh

RUN echo $(date -u '+%Y-%m-%d %H:%M:%S') >> ${BUILDLOGFILE}
RUN echo "FStar version => ${COMMITID}" >> ${BUILDLOGFILE}
RUN ./build_helper.sh ${TARGET} ${BUILDLOGFILE} ${MAXTHREADS} ${BRANCHNAME} || true
RUN echo $(date -u '+%Y-%m-%d %H:%M:%S') >> ${BUILDLOGFILE}

# Generate query-stats.
# List the hints that fail to replay.
RUN bash -c ".scripts/query-stats.py -f ${BUILDLOGFILE} -F html -o log_no_replay.html -n all '--filter=fstar_usedhints=+' '--filter=fstar_tag=-' -g"

# Worst offenders (longest times)
RUN bash -c ".scripts/query-stats.py -f ${BUILDLOGFILE} -F html -o log_worst.html -c -g -n 10"

# Remove ssh identities.
RUN rm ${MYHOME}/.ssh/id_rsa
RUN eval $(ssh-agent) && ssh-add -D