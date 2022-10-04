# Alloy

> Alloy is a language for describing structures and a tool for exploring them. It has been used in a wide range of applications from finding holes in security mechanisms to designing telephone switching networks.
> 
> https://alloytools.org/about.html


```Alloy
sig Name, Addr {}
sig Book {
    addr: Name -> lone Addr
}

pred show (b: Book) {
    #b.addr > 1
}

run show for 3 but 1 Book
```

# 参考
- https://alloytools.org/about.html
- 抽象によるソフトウェア設計 ―Alloyではじめる形式手法, https://www.ohmsha.co.jp/book/9784274068584/
- http://softwareabstractions.org/models/a4-models-index.html
