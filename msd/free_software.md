# GNU GPLと自由なソフトウェアについて

### 自由なソフトウェア(Free Software)とは
勘違いされやすいのだが、フリーソフトウェアとは"自由な"ソフトウェアのことを指すのであって、"無料の"ソフトウェアを指すものではない
(実際に有料のフリーソフトウェアも(少ないが)存在する)。  
この勘違いは英語圏でもよく起こっている(そもそもFreeが"無料"と"自由"の2つの意味を持つことが原因なので)。
GNUプロジェクトの創始者であるリチャード・ストールマン導師は「日本語にはせっかく2つの意味を区別する言葉があるのだから、フリーソフトウェアではなく自由なソフトウェアと呼んで欲しい」と述べている。
具体的に自由ソフトウェアで守られる自由とは、下の4つの自由を指す。  

> A program is free software if the program's users have the four essential freedoms:  
> - The freedom to run the program as you wish, for any purpose (freedom 0).  
> - The freedom to study how the program works, and change it so it does your computing as you wish (freedom 1). Access to the source code is a precondition for this.  
> - The freedom to redistribute copies so you can help others (freedom 2).  
> - The freedom to distribute copies of your modified versions to others (freedom 3). By doing this you can give the whole community a chance to benefit from your changes. Access to the source code is a precondition for this.

(Cited from [What is free software? -GNU Project- Free Software Foundation](https://www.gnu.org/philosophy/free-sw.en.html))

> あるプログラムが自由ソフトウェアであるとは、そのプログラムの利用者が、以下の四つの必須の自由を有するときです:  
> - どんな目的に対しても、プログラムを望むままに実行する自由 (第零の自由)。  
> - プログラムがどのように動作しているか研究し、必要に応じて改造する自由 (第一の自由)。ソースコードへのアクセスは、この前提条件となります。  
> - ほかの人を助けられるよう、コピーを再配布する自由 (第二の自由)。  
> - 改変した版を他に配布する自由 (第三の自由)。これにより、変更がコミュニティ全体にとって利益となる機会を提供できます。ソースコードへのアクセスは、この前提条件となります。

(引用元: [自由ソフトウェアとは? - GNUプロジェクト - フリーソフトウェアファウンデーション](https://www.gnu.org/philosophy/free-sw.ja.html))

上の条件にソフトウェアが有料か無料かについて条件が無いように、自由ソフトウェアを有料で配布することもできる。  
しかし、上の条件にあるように自由ソフトウェアはそれを受け取った人が別の人に無制限に再配布することができるので、  
(単純に作成したソフトウェアを売るというビジネスモデルでは)自由ソフトウェアで利益を得ることは難しい。  

## GNU GPL (General Public License)
GNU GPLとは、フリーソフトウェアライセンスの1つであり、プログラムの利用者に上の4つの自由を認めている。  
GPL の最大の特徴はGPLで提供されているプログラムを改変したり、組み込んで作られたプログラム(二次的著作物、派生物)は、  
それもまたGPLでライセンスされて提供される必要があるということである。  

### GPLで許諾されたプログラムをライブラリとして使う場合
GPLで提供されているライブラリとリンクする別のプログラムを作った場合、このプログラムのライセンスはGPLにしなければならないだろうか？  
これは、(FSFの見解としては)明確にYESである。  
動的リンク・静的リンクにかかわらず、GPLであるプログラムにリンクするプログラムはGPLで提供されなければならない。  
[https://www.gnu.org/licenses/gpl-faq.ja.html#GPLStaticVsDynamic]  

しかし、ライブラリとして利用されること目的としてプログラムを配布する場合にはこの制約は強すぎることがある。  
例えば、GPLでライセンスされる標準Cライブラリとそのライブラリをリンクするコンパイラ(+ツールチェイン)があったとき、  
そのコンパイラでコンパイルされたプログラムはすべてGPLになってしまう。  

そこで、GPLよりも制約を弱めたLGPLというライセンスが存在する。  
LGPLは元々はLibrary General Public License(現在ではLesser General Public License)の略で、  
その名前の通りライブラリとして提供するプログラムに対して適用することを目的として作られたライセンスである。  

LGPLで許諾されているライブラリについては、次の条件で使用できる
1. ライブラリ自体を改変する場合  
   -> 改変したライブラリもLGPL又はGPLで配布しなければならない
1. ライブラリ自体は改変せずに、単にリンクして使う場合  
   -> (共通事項として)アプリケーションのリバースエンジニアリングを禁止してはならない  
   1. 静的にリンクする場合  
      -> プログラムの利用者がライブラリを改変してアプリケーションと再リンクできるようにするため、  
         ソースコード又は未リンク状態のオブジェクトファイルを提供しなければならない(必ずソースコードを提供しなければならないというわけではない)  
   1. 動的リンクするが、ライブラリとアプリケーションをまとめて配布する場合  
      -> ライブラリのソースを含めて配布する又はライブラリのソースのURLを記載するなどする
   1. 動的リンクして、ライブラリは配布しない場合  
      -> 特に制約は無い  
[https://www.gnu.org/licenses/gpl-faq.ja.html#LGPLStaticVsDynamic]

例えばGNUの標準Cライブラリの実装であるglibcはLGPLで提供されているため、  
GCCでコンパイルしたCプログラムが全てGPLになってしまうというようなことは無い。  
また、GNUの標準C++ライブラリの実装であるlibstdc++はGPLで提供されているが、  
こちらはGCCランタイムライブラリ例外という特別な条項が付与されており、  
GCCでコンパイルしたC++プログラムが全てGPLになってしまうということも無い。  
[https://www.gnu.org/licenses/gcc-exception-3.1-faq.ja.html]

ちなみに、ライブラリとリンクしたプログラムがライブラリの二次派生物であるとする解釈はあくまでFSFの独自の見解であって、  
実際に裁判になったときに各国の裁判所がどのような判断を下すかはまた別の問題である。    

この問題に対する解釈は法律の専門家の間でも議論があるらしく、FSFの見解とは別に  
「静的リンクは二次派生物を構成するが、動的リンクはそうでない」という解釈や  
「静的・動的にかかわらずリンクは二次派生物を構成しない」という見解もある。  

#### ヘッダファイルのinclude
LGPLによって許諾されているライブラリをリンクする場合、普通はそのライブラリのヘッダファイルをプログラムの中でincludeすることになる。  
しかしヘッダファイルのincludeとは要するにソースコードのコピペであり、ソースコードの改変にあたるとも考えられる。  
とはいえ、LGPLで提供されているライブラリのヘッダファイルをincludeしただけでそのプログラムもLGPLになってしまうのではまるで意味が無いので、  
LGPLの条項にはヘッダファイルについての規定が書かれている。  

LGPLv3
> 3. Object Code Incorporating Material from Library Header Files.  
> The object code form of an Application may incorporate material from a header file that is part of the Library.  
> You may convey such object code under terms of your choice, provided that, if the incorporated material is not  
> limited to numerical parameters, data structure layouts and accessors, or small macros, inline functions and  
> templates (ten or fewer lines in length), you do both of the following:  
>  a) Give prominent notice with each copy of the object code that the Library is used in it and that the Library and its use are covered by this License.  
>  b) Accompany the object code with a copy of the GNU GPL and this license document.  

(Cited from [https://www.gnu.org/licenses/lgpl-3.0.ja.html])  

非公式日本語訳
> 3. ライブラリのヘッダファイルに由来するコードや各種データを取り込ん だオブジェクトコード  
> オブジェクトコード形式の『アプリケーション』は、『ライブラリ』の一部で あるヘッダファイルに含まれるコードや各種データを取り込むことができる。  
> あなたは、そのようなオブジェクトコードを、あなたが選択したいかなる条項 の下でも複製、伝達して構わない。  
> ただし、取り込まれたコード等が数値的パラメータや、データ構造のレイアウトやアクセサー、小さなマクロ、  
> インライン関数やテンプレート(長さにして10行以下)ではない場合、あなたは以下の両方を行わなければならない。  
> a) オブジェクトコードのコピーそれぞれにおいて、『ライブラリ』がその中で利用されており、『ライブラリ』とその利用は本許諾書によって保護されている旨を目立つように告知する。  
> b) オブジェクトコードに、GNU GPLと本許諾書のコピーを添付する。  

([https://mag.osdn.jp/07/09/05/017211] より引用)  

またヘッダファイルが著作権保護の対象となるかは微妙な問題である。  
例えばヘッダファイルだけで提供されることが目的のライブラリならば、ほぼ確実に著作権による保護の対象となる。  
また独自に作ったプログラムのヘッダファイルならば、これも恐らく保護の対象になる(Java APIについての裁判の結果より)。  
しかし、標準Cライブラリのように規格で定められたライブラリのヘッダファイルは著作権による保護対象にならない可能性がある。  
### 非GPLなライブラリをリンクしたプログラムをGPLで配布する場合
ライブラリがLGPL又はランタイムライブラリ例外の適用されるGPLで提供されている場合、  
それらのライブラリをリンクしたプログラムをプロプライエタリなどの非GPLなライセンスで提供することができることが分かった。  
しかし、非GPLなライセンスで配布されているライブラリとリンクするプログラムをGPLで配布するということはできるだろうか？

これは、利用するライブラリが実際にどのようなライセンスであるかによる。  
例えばMITや修正BSDといったライセンスは二次著作物のライセンスについて何も規定していないので、  
これらのライセンスで提供されているライブラリを使ってプログラムを作成する場合自由にライセンスを選ぶことができる(もちろんGPLにすることもできる)。  
このようなライセンスのことを(GPLと)互換性のあるライセンスという。  

一方で、(フリーソフトウェアライセンスであっても)GPLと互換性の無いライセンスも存在する。  
例えばオリジナルのBSDライセンスには次の条項が存在する。  
> 3. All advertising materials mentioning features or use of this software must display the following acknowledgement: This product includes software developed by the University of California, Berkeley and its contributors.  

これは俗に「宣伝条項」と呼ばれるもので、もちろんGPLには存在しない制約である。  
したがって、オリジナルBSDライセンスで提供されるライブラリとリンクしたプログラムを(プレーンな)GPLでライセンスして配布することはできない  
(GPLの条項に「宣伝条項」を加えた新しいライセンスでプログラムを配布することはできる)。  

GPLで提供された他のライブラリとオリジナルBSDライセンスで提供されるライブラリの両方を使う場合はより問題が深刻になる。  
というのも、GPLは使用や頒布に関して追加の制限を課すことを禁止しているので、GPLとBSDという矛盾するライセンスのライブラリを  
同時に使ってプログラムを作ることは(ライブラリの権利者に頼んでライセンスを変更してもらう等の対応をしない限り)不可能である。  
(参考: [https://mag.osdn.jp/06/06/09/1537222])

実際にv3未満のOpenSSLはGPLと非互換なライセンスで公開されていたため、OpenSSLとリンクするプログラムはGPLにできないという問題があった。  
例えばGNU WgetはOpenSSLとリンクするため、プレーンなGPLでなく特別な例外条項付きのライセンスで公開されている。  
[https://ja.wikipedia.org/wiki/OpenSSL#%E3%83%A9%E3%82%A4%E3%82%BB%E3%83%B3%E3%82%B9]
[https://ja.wikipedia.org/wiki/GNU_Wget#%E3%83%A9%E3%82%A4%E3%82%BB%E3%83%B3%E3%82%B9]

#### システムライブラリ例外
Visual C++でWindowsアプリケーションを作る場合、プログラムはMicrosfotの提供する(非GPLな)標準C++ライブラリとリンクされる。  
つまり、Visual C++でコンパイルされたプログラムは(プレーンな)GPLで配布することができないということになってしまう。  

そこで、GPLにはシステムライブラリ例外という例外規定が定められている。  
これは、プログラムが(動的に)リンクするライブラリがOSによって提供されており、  
プログラムと共に配布されない場合にはそのようなライブラリはGPLに適合していなくても良いという規定である。  
[https://www.gnu.org/licenses/gpl-faq.ja.html#WindowsRuntimeAndGPL]

### リンク以外の方法でプログラムを利用する場合
GPLで提供されているプログラムをリンクした場合、リンクしたプログラムもまたGPLになることは述べたが、
リンク以外の方法でGPLなプログラムを利用した場合はどうなるだろうか？

極端な話、GPLで許諾されているサーバープログラムがあった場合、  
それとHTTPで通信するクライアントプログラムもGPLで提供する必要があるだろうか？  
この答えはもちろんNOである。  

FSFの解釈ではプログラムの独立性はプロセス(メモリ空間)単位であるとされており、  
動的にリンクされ同一プロセスで実行されるプログラムは二次派生物となるが、  
fork/execで起動されるなどの別プロセスからプロセス間通信を行うプログラムは(基本的に)二次派生物とならないとしている。  
[https://www.gnu.org/licenses/gpl-faq.ja.html#MereAggregation]
[https://www.gnu.org/licenses/gpl-faq.html#GPLAndPlugins]
[https://www.gnu.org/licenses/gpl-faq.html#GPLPluginsInNF]

しかしこれ、MMUが無くてプロセス毎のメモリ空間の分離が行われないマイコン上で動くプログラムとかはどういう扱いになるのだろう…?  
(問答無用ですべてGPLになるのだろうか？)  

## GPLv2 と GPLv3 の違い

### 特許条項
GPLv2はプログラムに含まれる特許についての扱いは何も定めておらず、GPLで許諾してプログラムを配布するが、  
そのプログラムが意図しない目的で利用された場合などにプログラムの利用者を特許権侵害で訴えるということが可能であった。  
これは明らかにGPLの理念に反することなので、GPLv3からは特許権に関する条項が追加され、特許権を持つものがGPLv3で許諾して  
プログラムを配布した場合、そのプログラムの利用者に特許の利用を認めなくてはならないということになった。  

### Tivoization
Tivoization(Tivo化)とは、ハードウェアに特定のソフトウェアしか動かせないような細工を施すことを指す。  
これはTivoという会社のハードディスクレコーダーの例が有名になったためにこう呼ばれるようになった。  
Tivo社はハードウェにLinuxカーネルをインストールした状態で製品を出荷してしたが、このハードウェアには  
予め(Tivo社により)電子署名されたプログラムしか動作しないという細工が施されていた。  
これではGPLによりプログラムの改変が許されていたとしても、実際に改変したプログラムを動かすことができないので  
GPLに理念に反している。  
このためGPLv3ではTivo化を制限する条項が設けられた。  

一方で、実際にTivo社の例で使用されたLinuxカーネルのライセンスはGPLv2のままである。  
リーナス・トーバルズ自身は、ソフトウェアライセンスはソフトウェアを対象とするのであって、  
それを動作させるハードウェアについては関知しないべきだとしている。  
また実際問題としてLinuxカーネルをGPLv2からGPLv3に移行するにはLinuxカーネルの全著作権者の了承を得る必要があるので  
ライセンスの移行は事実上不可能である。

Linuxカーネルを利用するAndroidデバイスではまさにこのような問題が起こっている。  
現代のほぼ全てのスマートフォンはセキュリティ上の理由から電子署名されたソフトウェアのみを実行する(制限ブート)ようになっているため、  
Androidを搭載したスマートフォンの利用者が自身のスマートフォンに別のOSをインストールしようとする場合、  
何らかの方法でこのような制限を突破する必要がある。  
(ハードウェアベンダーによってはブートローダーのアンロック方法が公開されており、  
そのような場合は公開された手順に従えば好きなOSをインストールすることができる。  
そうでない場合は何らかのセキュリティホールを使って制限を突破する必要がある。)  

またWindowsPCの場合にもセキュアブートという似たような仕組みがあるが、こちらはWindowsのOEM条件として  
BIOS上でセキュアブートを無効化する方法と、信頼する電子署名の秘密鍵を変更する方法を用意することが定められているので  
利用者は自由にOSをインストールして使うことができる。  

## まとめ
GNU GPLは分かりづらい。  
まずもってFSFの見解が分かりづらい上に、微妙な例外的状況のことが書かれていなくて分かりづらい(スクリプト言語の場合のことも良く分からん)。  
しかもFSFの見解が分かったとしても最終的には著作権法の問題になるので実際に裁判が起きて判決が出るまで何も分からないということになる。  
みんなMIT/修正BSD/Apacheとかの別のライセンスを使おう。  
ただLinux KernelがGPLv3だったら今頃市販のスマホ上で自由にOSをインストールしたりできたはずなので、そこは残念である。  

## 参考資料
[https://www.gnu.org/licenses/gpl-3.0.html]
[https://www.gnu.org/licenses/old-licenses/gpl-2.0.html]
