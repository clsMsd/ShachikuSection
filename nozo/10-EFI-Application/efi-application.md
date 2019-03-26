# UEFIアプリケーションの紹介

## UEFIとは？
> ## WHAT IS UEFI?
> UEFI stands for "Unified Extensible Firmware Interface." The UEFI Specification defines a new model for the interface between personal-computer operating systems and platform firmware. The interface consists of data tables that contain platform-related information, plus boot and runtime service calls that are available to the operating system and its loader. Together, these provide a standard environment for booting an operating system and running pre-boot applications.
> 
> [UEFI Forum](https://uefi.org/)

ファームウェアとOSの間のインターフェース仕様。
OSの起動や、起動する前のアプリケーションを実行するための環境を提供する。

[UEFI Forum](https://uefi.org/)によって仕様が定められている。
- [UEFI Specification Version 2.7 (Errata A)](http://www.uefi.org/sites/default/files/resources/UEFI%20Spec%202_7_A%20Sept%206.pdf)

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
- [UEFI Forum](https://uefi.org/)
- [UEFI - ArchWiki - Arch Linux](https://wiki.archlinux.jp/index.php/Unified_Extensible_Firmware_Interface)
