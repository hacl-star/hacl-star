# hacl build container

# Define on fstar-version.json what FStar base container image
# hacl build should use.
# By default it always look for the latest FStar container available
# In case you would like to reference a specific commit,
# replace latest with the commit id from github using 12 characters.
ARG DOCKERHUBPROJECT
ARG COMMITID
FROM ${DOCKERHUBPROJECT}fstar-linux:${COMMITID}

ARG BUILDLOGFILE
ARG MAXTHREADS
ARG TARGET
ARG BRANCHNAME

# ADD SSH KEY
RUN mkdir -p ${MYHOME}/.ssh
RUN chown everest ${MYHOME}/.ssh
RUN chmod 700 ${MYHOME}/.ssh
COPY --chown=everest id_rsa ${MYHOME}/.ssh/id_rsa
RUN chmod 600 ${MYHOME}/.ssh/id_rsa

# Copy source files
RUN mkdir ${MYHOME}/hacl-star
COPY --chown=everest / ${MYHOME}/hacl-star/

# Do some cleanup
RUN rm -f build.sh
RUN rm -f build_helper.sh
RUN rm -f buildlogfile.txt
RUN rm -f log_no_replay.html
RUN rm -f log_worst.html
RUN rm -f orange_status.txt
RUN rm -f result.txt
RUN rm -f status.txt
RUN rm -f commitinfofilename.json

RUN rm hacl-star/Dockerfile
RUN rm hacl-star/build.sh
RUN rm hacl-star/build_helper.sh
RUN rm hacl-star/id_rsa
RUN rm hacl-star/commitinfofilename.json

COPY --chown=everest build.sh ${MYHOME}/build.sh
RUN chmod +x build.sh
COPY --chown=everest build_helper.sh ${MYHOME}/build_helper.sh
RUN chmod +x build_helper.sh

RUN ./build_helper.sh ${TARGET} ${BUILDLOGFILE} ${MAXTHREADS} ${BRANCHNAME} || true

# Remove ssh identities.
RUN rm ${MYHOME}/.ssh/id_rsa