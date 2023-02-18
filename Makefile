all:
	cd tex_source ; make ; cd ..

clean:
	cd tex_source ; make clean ; cd .. 
	rm -rf frama_c_tutorial.pdf

