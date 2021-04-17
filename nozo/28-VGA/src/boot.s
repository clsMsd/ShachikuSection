[BITS 16]

entry:
    cli
    mov ax, 0
    mov ds, ax
    mov es, ax
    mov ss, ax
    mov sp, 0x7C00
    sti

    ; vide mode = 0x12 (VGA 640*480 16 color)
    mov ax, 0x0012
    int 0x10

    mov ah, 0b1011 ; データレジスタ(----IRGB)
    mov al, 0x02 ; アドレスレジスタ
    mov dx, 0x03C4 ; VGA制御のI/Oポートアドレス
    out dx, ax

    mov ax, 0xA000
    mov es, ax
    mov [es:0x0000], byte 0xFF



stop:
    jmp $

    times 510 - ($ - $$) db 0
    db 0x55, 0xAA

