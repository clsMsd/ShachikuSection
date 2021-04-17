all:
	nasm -f elf32 -g3 -F dwarf boot.s -o boot.o
	ld -Ttext=0x7c00 -melf_i386 boot.o -o boot.elf
	objcopy -O binary boot.elf boot.img

clean:
	rm -f *.o *.elf *.bin *.img

run: all
	qemu-system-i386 boot.img

debug: all
	qemu-system-i386 -s -S boot.img & \
	gdb boot.elf \
		-ex 'target remote localhost:1234' \
		-ex 'set pagination off' \
		-ex 'layout src' \
		-ex 'layout regs' \
		-ex 'break entry' \
		-ex 'break stop' \
		-ex 'continue'