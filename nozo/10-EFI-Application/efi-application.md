# UEFIアプリケーションの紹介

## UEFIアプリケーションとは？

> UEFI のブートプロセス
> 1. システムのスイッチが入る - POST (Power On Self Test) プロセス
> 1. UEFI ファームウェアがロードされます。ファームウェアは起動に必要なハードウェアを初期化します
> 1. 次にファームウェアはブートマネージャのデータを読み込みどの UEFI アプリケーションをどこから (つまりどのディスク・パーティションから) 起動するか決定します
> 1. ファームウェアのブートマネージャのブートエントリに定義されているように UEFI アプリケーションをファームウェアが起動します
> 1. 起動した UEFI アプリケーションは設定によって他のアプリケーション (UEFI シェルや rEFInd の場合) やカーネルと initramfs (GRUB などのブートローダの場合) を起動します

## VMでUEFIのテスト
[OVMF · tianocore/tianocore.github.io Wiki · GitHub](https://github.com/tianocore/tianocore.github.io/wiki/OVMF)

## UEFI shell

## UEFIアプリケーション

## 参考文献
- [UEFI - ArchWiki - Arch Linux](https://wiki.archlinux.jp/index.php/Unified_Extensible_Firmware_Interface)
