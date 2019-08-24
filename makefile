all: compile

compile:
	java -jar ../jtb132di.jar -te minijava.jj
	java -jar ../javacc5.jar minijava-jtb.jj
	javac *.java

clean:
	rm -f *.class *~
