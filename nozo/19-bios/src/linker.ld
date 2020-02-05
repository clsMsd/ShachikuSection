ENTRY("_start")

SECTIONS
{
	. = 0xfff0;
	
	.text : {
	      *(.text)
	}
}
