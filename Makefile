JAR=tla2tools.jar
JAR_URL=https://github.com/tlaplus/tlaplus/releases/download/v1.7.3/tla2tools.jar

# Download the JAR if it does not exist
$(JAR):
	wget --no-check-certificate --content-disposition -O $@ $(JAR_URL)

# Don't redownload stuff every time
.PRECIOUS: $(JAR)


pcal: tla2tools.jar ReliableBroadcast.tla
	java -cp tla2tools.jar pcal.trans ReliableBroadcast.tla

tlc: tla2tools.jar ReliableBroadcast.tla TLCReliableBroadcast.cfg TLCReliableBroadcast.tla
	java -XX:+UseParallelGC -jar tla2tools.jar -config TLCReliableBroadcast.cfg -workers 4 TLCReliableBroadcast.tla

.PHONY: pcal tlc
