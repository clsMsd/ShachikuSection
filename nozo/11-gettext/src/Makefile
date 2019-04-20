CFLAGS = -Wall -Wextra
LDFLAGS = -lintl

EXEC = hello

all: $(EXEC) locale/ja/LC_MESSAGES/$(EXEC).mo

$(EXEC): $(EXEC).c 
    $(CC) $(CFLAGS) $(CPPFLAGS) -o $@ $< $(LDFLAGS)

locale/ja/LC_MESSAGES/$(EXEC).mo: locale/ja/LC_MESSAGES/$(EXEC).po
    msgfmt --output-file=$@ $<

locale/ja/LC_MESSAGES/$(EXEC).po: locale/$(EXEC).pot
    msgmerge --update $@ $<

locale/$(EXEC).pot: $(EXEC).c
    xgettext -k_ -j -lC -c -s -o $@ $<

clean:
    @rm -f $(EXEC) locale/ja/LC_MESSAGES/*.mo *~

.PHONY: clean