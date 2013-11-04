/******************************************************************************
 * main.c
 *
 * treetop - A 'top' like text/log file monitor.
 *
 * Copyright (C) 2013, Matt Davis (enferex)
 *
 * This file is part of treetop.
 * treetop is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 2 of the License, or
 * (at your option) any later version.
 *
 * treetop is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with treetop.  If not, see <http://www.gnu.org/licenses/>.
 *****************************************************************************/


#define _WITH_GETLINE
#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <signal.h>
#include <fcntl.h>
#include <libgen.h>
#include <unistd.h>
#include <curses.h>
#include <errno.h>
#include <menu.h>
#include <panel.h>
#include <pthread.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/ioctl.h>
#ifdef HAVE_SYS_EVENT_H
#include <sys/event.h>
#endif /* !HAVE_SYS_EVENT_H */


/* Output routines */
#define _PR(_tag, _outfd, ...)                       \
    do {                                             \
        fprintf(_outfd, "[logtop]"_tag __VA_ARGS__); \
        fputc('\n', _outfd);                         \
    } while(0)
#define PR(...)  _PR(" ", stdout, __VA_ARGS__)
#define DBG(...) _PR("[debug] ", stdout, __VA_ARGS__)
#define WR(...)  _PR("[warning] ", stderr, __VA_ARGS__)
#define ER(...)                               \
    do {                                      \
        _PR("[error] ", stderr, __VA_ARGS__); \
        exit(-1);                             \
    } while (0)


/* Comment character for config file (anything after this char is ignored) */
#define COMMENT_CHAR '#'


/* If the file has the 'UPDATED' state */
#define UPDATED_CHAR "*"


/* Default delay (seconds) */
#define DEFAULT_TIMEOUT_SECS 10


/* Max */
#define MAX(_a, _b) (((_a)>(_b)) ? (_a) : (_b))


/* Window dimensions */
#define INNER_WIN_LINES (LINES-3)
#define INNER_WIN_COLS (COLS-2)


#define TITLE "}-= TreeTop =-{"

/* File state */
typedef enum _state_e
{
    UNCHANGED,
    UPDATED
} state_e;

/* Stores the last X window columns number */
static int columns = 0;

/* Mutex to protect post_menu calls */
static pthread_mutex_t mtx_post_menu;

/* Mutex to protect doupdate calls */
static pthread_mutex_t mtx_update_panels;

/* File information */
typedef struct _data_t
{
    int fd;
    FILE *fp;
    const char *full_path;
    const char *base_name;
    char *line; /* pointer to the last line in buff */
    char *buff; /* file content */
    struct _data_t *next;
    state_e state;
    ITEM *item;  /* Curses menu item for this file */
    time_t last_mod;
} data_t;

/* Screen (ncurses state and content) */
typedef struct _screen_t
{
    WINDOW *master;  /* Nothing here it just needs a border to look pretty */
    WINDOW *content; /* Menu goes here                                     */
    WINDOW *details; /* Display details about selected item                */
    PANEL  *master_panel;
    PANEL  *content_panel;
    PANEL  *details_panel;
    MENU *menu;
    ITEM **items;
    data_t *datas;
} screen_t;

/* Param to a thread */
typedef struct _thread_param_t
{
    int opened_files;
    screen_t *master_screen;
} thread_param_t;

static void get_last_line(data_t *d);
const data_t *show_details;

static void usage(const char *execname, const char *msg)
{
    if (msg)
      PR("%s", msg);
    printf("Usage: %s <config> [-d secs] [-h]\n"
       "    -h:      Display this help screen\n"
       "    -d secs: Auto-update display every 'secs' seconds\n", execname);
    exit(0);
}

/* Returns the starting x-coordinate such that when displaying a value of
 * 'length' characters long, it will be centered in the given window.
 */
static int find_center_start(const WINDOW *win, size_t length)
{
    int max_x = getmaxx(win);
    int half = length / 2;
    return max_x / 2 - half;
}


/* Writes the program title into the window */
static void write_title_window(WINDOW *master)
{
    int x;
    box(master, 0, 0);
    x = find_center_start(master, strlen(TITLE));
    mvwprintw(master, 0, x, TITLE);
}

static void read_files(int bytes, int opened_files, data_t *data) {
    char c;
    int j;
    char *last, *tmp;
    data_t *d;


    for (d = data; d; d = d->next)
    {
        if (d->state == UPDATED) {
            if (d->buff == NULL) {
                if ((d->buff = malloc(sizeof(char) * bytes)) == NULL) {
                    ER("Can't allocate memory for file buffer");
                }
            }
            else if (bytes * sizeof(char) != sizeof(d->buff)) {
                if ((tmp = realloc(d->buff, sizeof(char) * bytes)) == NULL) {
                    ER("Can't reallocate memory for file buffer");
                }
                d->buff = tmp;
            }
            memset(d->buff, '\0', sizeof(char) * bytes);
            /* Set the file-read pointer */
            if (fseek(d->fp, -bytes, SEEK_END) == -1)
                fseek(d->fp, 0, SEEK_SET);

            j=0;
            last = d->buff;
            while ((c = fgetc(d->fp)) != EOF)
            {
                d->buff[j] = c;
                if (j > 0 && d->buff[j-1] == '\n') {
                    last = d->buff + j;
                }
                j++;
            }
            d->buff[j] = '\0';
            d->line = last;
        }
    }
}

/* returns the writable bytes of the s WINDOW */
static int getMaxBytes(WINDOW *s, int *maxx, int *maxy) {
    getmaxyx(s, *maxy, *maxx);

    *maxy -= 2; /* Ignore border */
    *maxx -= 2; /* Ignore border */
    return *maxx * *maxy;

}

static void refresh_menus(screen_t *screen)
{
    pthread_mutex_lock(&mtx_post_menu);
    unpost_menu(screen->menu);
    post_menu(screen->menu);
    pthread_mutex_unlock(&mtx_post_menu);
}

static void update_panels_safe()
{
    pthread_mutex_lock(&mtx_update_panels);
    update_panels();
    doupdate();
    pthread_mutex_unlock(&mtx_update_panels);
}

static void menu_driver_update(screen_t *screen, int c)
{
    data_t *d;
    if (c >= 0)
    {
        menu_driver(screen->menu, c);
    }

    for (d=screen->datas; d; d=d->next)
    {
        if (d->state == UPDATED)
        {
            d->item->description.str = d->line;
        }
    }
    refresh_menus(screen);
    for (d=screen->datas; d; d=d->next)
    {
        if (d->state == UPDATED)
        {
            if (d != ((data_t *)(item_userptr(current_item(screen->menu)))))
            {
                mvwprintw(screen->content, item_index(d->item), 3, UPDATED_CHAR);
            }
            else {
                d->state = UNCHANGED;
            }
        }
    }

    if (c > 0)
    {
        update_panels_safe();
    }
}

static void *thread_read_files(void *args)
{
    char c;
    int i, opened_files, maxx, maxy;
#ifdef HAVE_KQUEUE
    int kq;
    struct kevent *ev;
#elif defined(HAVE_EPOLL_CREATE)
    int epollfd;
    struct epoll_event *ev;
#endif /* !HAVE_KQUEUE */
    screen_t *screen;
//    struct stat stats;
    data_t *data, *d;//, *show_details = NULL;

    opened_files = ((thread_param_t *)args)->opened_files;
    screen = ((thread_param_t *)args)->master_screen;
    data = screen->datas;

    free(args);

#ifdef HAVE_KQUEUE
    kq = kqueue();
    if (kq < 0)
        {
        ER("Can't initialize kqueue");
    }
#elif defined(HAVE_EPOLL_CREATE)
    epollfd = epoll_create1(0);
    if (epoll_create1 < 0)
    {
       ER("Can't initialize epoll: %s", strerror(errno));
    }
#endif /* !HAVE_KQUEUE */

#ifdef HAVE_KQUEUE
    ev = (struct kevent *) malloc(sizeof(struct kevent) * opened_files + 3); /* allocate three extra events to get the notifications from the event loop */
    if (ev == NULL)
    {
        ER("Can't allocate memory for kevents");
    }
#elif defined(HAVE_EPOLL_CREATE)
#endif /* !HAVE_KQUEUE */

#ifdef HAVE_KQUEUE
    i = 0;
    for (d=screen->datas; d; d=d->next)
    {
        EV_SET(&ev[i], d->fd, EVFILT_VNODE, EV_ADD | EV_ENABLE | EV_CLEAR, NOTE_DELETE | NOTE_RENAME, 0, 0); /* Detect removal and renamming of the file */
        EV_SET(&ev[i], d->fd, EVFILT_READ, EV_ADD | EV_ENABLE | EV_CLEAR, 0, 0, 0); /* Detect new data */
        i++;
    }
    EV_SET(&ev[i++], SIGWINCH, EVFILT_SIGNAL, EV_ADD | EV_ENABLE, 0, 0, 0);
    EV_SET(&ev[i++], SIGUSR1, EVFILT_SIGNAL, EV_ADD | EV_ENABLE, 0, 0, 0);
    EV_SET(&ev[i++], SIGUSR2, EVFILT_SIGNAL, EV_ADD | EV_ENABLE, 0, 0, 0);
#endif /* !HAVE_KQUEUE */

#ifdef HAVE_KQUEUE
    if (kevent(kq, ev, opened_files + 3, NULL, 0, NULL) < 0) {
        ER("Can't set kevent");
    }
#endif /* !HAVE_KQUEUE */

    for (;;) {
        read_files (getMaxBytes(screen->details, &maxx, &maxy), opened_files, data);

        if (show_details == NULL) {
            menu_driver_update(screen, -1);
            hide_panel(screen->details_panel);
        }
        else {
            wmove(screen->details, 1, 1);
            i = 0;
            while ((c = show_details->buff[i++]) != '\0') {
                if (getcurx(screen->details) == maxx)
                {
                    waddch(screen->details, ' ');
                    waddch(screen->details, ' ');
                    waddch(screen->details, ' ');
                }
                else if (getcurx(screen->details) == 0)
                    waddch(screen->details, ' ');

                waddch(screen->details, c);
            }

            /* Display file name and draw border */
            box(screen->details, 0, 0);
            mvwprintw(screen->details, 0, 1, "[%s]", show_details->base_name);
            show_panel(screen->details_panel);
        }

        update_panels_safe();

#ifdef HAVE_KQUEUE
        i = kevent(kq, NULL, 0, ev, 1, NULL);
        if (i > 0) {
            if (ev->filter == EVFILT_SIGNAL &&
                ev->ident == SIGWINCH) {

                /* This ensure that LINES and COLS are correctly updated */
                doupdate();

                mvwprintw(screen->master, 1, columns-1, " ");
                columns = COLS;
                if (wresize(screen->master, LINES, COLS) == ERR)
                    WR("Error resizing master windows");
                if (wresize(screen->content,
                            INNER_WIN_LINES, INNER_WIN_COLS) == ERR)
                    WR("Error resizing content windows");
                if (wresize(screen->details,
                            INNER_WIN_LINES, INNER_WIN_COLS) == ERR)
                    WR("Error resizing details windows");

                /* Redraw the title and clean up the border */
                write_title_window(screen->master);
                refresh_menus(screen);
                update_panels_safe();
            }
            else if (ev->filter == EVFILT_SIGNAL &&
                     ev->ident == SIGUSR1) {
               /* handle displaying details here */
                show_details = item_userptr(current_item(screen->menu));
            }
            else if (ev->filter == EVFILT_SIGNAL &&
                     ev->ident == SIGUSR2) {
               /* handle displaying details here */
                show_details = NULL;
            }
            else if (ev->filter == EVFILT_READ) {
                for (d=screen->datas; d; d=d->next) {
                    if(d->fd == ev->ident) {
                        d->state = UPDATED;
                        break;
                    }
                }
            }
        }
        if (i < 0) {
            DBG("Error retrieving kevent, we might have been interrupted");
        }
#else  /* !HAVE_KQUEUE */
                /* If the files have been updated, grab the last line from the file */
                for (d=data; d; d=d->next)
                {
                    if (stat(d->full_path, &stats) == -1)
                        ER("Could not obtain file stats for: '%s'", d->base_name);

                    /* If the file has been modified since last check, update */
                    if (stats.st_mtime != d->last_mod)
                    {
                        d->last_mod = stats.st_mtime;
                        d->state = UPDATED;
                    }
                }
                usleep(25000);
#endif /* !HAVE_KQUEUE */
    }

    return (void *) NULL;
}

/* Update display */
static void screen_create_menu(screen_t *screen)
{
    int i = 0;
    data_t *d;
    char line[COLS];
    const char *def = "Updating...";

    /* Count number of data items */
    for (d=screen->datas; d; d=d->next)
      ++i;

    /* Allocate a long line for the description (make it all spaces) */
    memset(line, ' ', sizeof(line) - 1);
    line[sizeof(line)] = '\0';
    memcpy(line, def, strlen(def));

    /* Allocate and create menu items (one per data item */
    screen->items = (ITEM **)calloc(i+1, sizeof(ITEM *));
    for (i=0, d=screen->datas; d; d=d->next, ++i)
    {
        screen->items[i] = new_item(d->base_name, line);
        screen->items[i]->description.length = sizeof(line);
        set_item_userptr(screen->items[i], (void *)d);
        d->item = screen->items[i];
    }

    screen->menu = new_menu(screen->items);
    set_menu_mark(screen->menu, "-->  ");
    set_menu_win(screen->menu, screen->content);
    post_menu(screen->menu);
}



/* Initialize curses */
static screen_t *screen_create(data_t *datas, int timeout_ms)
{
    screen_t *screen;

    initscr();
    cbreak();
    noecho();
    curs_set(0); /* Turn cursor off */
    timeout(-1);
    keypad(stdscr, TRUE);

    screen = calloc(1, sizeof(screen_t));
    screen->datas = datas;

    /* Create the windows */
    screen->master = newwin(LINES, COLS, 0, 0);
    screen->content = newwin(INNER_WIN_LINES, INNER_WIN_COLS, 2, 1);
    screen->details = newwin(INNER_WIN_LINES, INNER_WIN_COLS, 2, 1);
    scrollok(screen->details, TRUE);

    /* Decorate the master window */
    write_title_window(screen->master);

    /* Put the windows in panels (easier to refresh things) */
    screen->master_panel = new_panel(screen->master);
    screen->details_panel = new_panel(screen->details);
    screen->content_panel = new_panel(screen->content);
    screen_create_menu(screen);
    return screen;
}


/* Cleanup from curses */
static void screen_destroy(screen_t *screen)
{
    nocbreak();
    echo();
    endwin();
    free(screen);
}

/* wrapper function for thread creation */
static pthread_t *threads_init(int opened_files, screen_t *screen) {
    thread_param_t *params;
    pthread_t *thread;

    /* Init the mutex which protects "post_menu" calls */
    if (pthread_mutex_init(&mtx_post_menu, NULL) < 0)
    {
      ER("Can't initiate post_menu mutex");
    }

    if (pthread_mutex_init(&mtx_update_panels, NULL) < 0)
    {
      ER("Can't initiate post_menu mutex");
    }

    thread = (pthread_t *) malloc(sizeof(pthread_t));
    if (thread == NULL) {
        ER("Can't allocate memory for reading threads");
    }

    params = (thread_param_t *) malloc(sizeof(thread_param_t));
    if (params == NULL) {
        ER("Can't allocate memory for thread params");
    }
    params->opened_files = opened_files;
    params->master_screen = screen;

    pthread_create(thread, NULL, thread_read_files, (void *)params);

    return (thread);
}

/* Create our file information */
static data_t *data_init(const char *fname, int *nb_of_opened_files)
{
    FILE *fp, *entry_fp;
    data_t *head, *tmp;
    char *c, *line;
    size_t sz;
    ssize_t ret;
#define CONTINUE {free(line); line=NULL; continue;}

    if (!(fp = fopen(fname, "r")))
      ER("Could not open config file '%s'", fname);

    /* For each line in config */
    head = NULL;
    line = NULL;
    while ((ret = getline(&line, &sz, fp)) != -1)
    {
        /* Skip whitespace */
        c = line;
        while (*c && isspace(*c))
          ++c;

        if (*c == COMMENT_CHAR)
          CONTINUE;

        /* Trim line */
        if (strchr(c, COMMENT_CHAR))
          *(strchr(c, COMMENT_CHAR)) = '\0';
        if (strchr(c, '\n'))
          *(strchr(c, '\n')) = '\0';
        if (strchr(c, ' '))
          *(strchr(c, ' ')) = '\0';

        if (strlen(c) == 0)
          CONTINUE;

        if (!(entry_fp = fopen(c, "r")))
        {
            WR("Could not open file: '%s'", c);
            CONTINUE;
        }

        /* Add to list */ 
        DBG("Monitoring file: '%s'...", c);
        tmp = head;
        head = calloc(1, sizeof(data_t));
        head->fp = entry_fp;
        head->fd = fileno(entry_fp);
        head->full_path = strdup(c);
        head->base_name = strdup(basename((char *)head->full_path));
        head->state = UPDATED; /* Force first update to process this */
        head->buff = NULL;
        head->next = tmp;
        free(line);
        line = NULL;
        (*nb_of_opened_files)++;

        if (fcntl(head->fd, F_SETFL, fcntl(head->fd, F_GETFL) & ~O_NONBLOCK ) == -1)
            ER("Can't set blocking to file %s", head->base_name);

    }

    return head;
}

static void threads_destroy(pthread_t *thread) {
    pthread_cancel(*thread);
    pthread_join(*thread, (void **) NULL);
    free(thread);
}

/* Cleanup */
static void data_destroy(data_t *datas)
{
    data_t *curr, *d = datas;

    while (d)
    {
        curr = d;
        fclose(d->fp);
        free(d->buff);
        d = curr->next;
        free(curr);
    }
}

/* Set the last line for this file */
static void get_last_line(data_t *d)
{
    ssize_t idx, n_bytes;
    char line[1024] = {0};

    /* Read in last 1024 bytes */
    if (fseek(d->fp, -sizeof(line), SEEK_END) == -1)
      fseek(d->fp, 0, SEEK_SET);
    n_bytes = fread(line, 1, sizeof(line)-1, d->fp);
    idx = n_bytes - 1;

    /* If file ends with newline */
    while (idx > 0 && (line[idx] == '\n' || line[idx] == '\r'))
      --idx;

    /* Now find the next newline */
    while (idx > 0 && (line[idx] != '\n' && line[idx] != '\r'))
      --idx;

    if (line[idx] == '\n' && idx+1 < n_bytes)
      ++idx;

    /* Copy starting from the last line */
    if (idx >= 0)
      strncpy(d->line, line+idx, sizeof(d->line) - 1);
}

/* Update data */
static void data_update(data_t *datas)
{
    data_t *d;
    struct stat stats;

    /* If the files have been updated, grab the last line from the file */
    for (d=datas; d; d=d->next)
    {
        if (stat(d->full_path, &stats) == -1)
          ER("Could not obtain file stats for: '%s'", d->base_name);

        /* If the file has been modified since last check, update */
        if (stats.st_mtime != d->last_mod)
        {
            get_last_line(d);
            d->last_mod = stats.st_mtime;
            d->state = UPDATED;
        }
    }
}


/* Update the details screen to display info about the selected item */
static void update_details(screen_t *screen, const data_t *selected)
{
    int c, maxx, maxy, bytes;

    /* Clear and get the size of the details window */
    wclear(screen->details);
    getmaxyx(screen->details, maxy, maxx);

    /* Draw last n bytes of file: (figure out how much room we have)   */
    maxy -= 2; /* Ignore border */
    maxx -= 2; /* Ignore border */
    bytes = maxx * maxy;

    /* Set the file-read pointer */
    if (fseek(selected->fp, -bytes, SEEK_END) == -1)
      fseek(selected->fp, 0, SEEK_SET);

    /* Read in file contents */
    wmove(screen->details, 1, 1);
    while ((c = fgetc(selected->fp)) != EOF)
    {
        /* Add whitespace if the cursor is on a border */
        if (getcurx(screen->details) == maxx)
        {
            waddch(screen->details, ' ');
            waddch(screen->details, ' ');
            waddch(screen->details, ' ');
        }
        else if (getcurx(screen->details) == 0)
          waddch(screen->details, ' ');

        waddch(screen->details, c);
    }

    /* Display file name and draw border */
    box(screen->details, 0, 0);
    mvwprintw(screen->details, 0, 1, "[%s]", selected->base_name);
}


/* Update display
 * 'show_details' is the selected item, if no item is slected this val is NULL
 */
static void screen_update(screen_t *screen, const data_t *show_details)
{
    data_t *d;

    /* Check for updated data */
    for (d=screen->datas; d; d=d->next)
      if (d->state == UPDATED)
        d->item->description.str = d->line;

    /* Refresh menu */
    unpost_menu(screen->menu);
    post_menu(screen->menu);

    /* Now draw a character signifying which file just changed */
    for (d=screen->datas; d; d=d->next)
    {
        if (d->state == UPDATED)
        {
            mvwprintw(screen->content, item_index(d->item), 3, UPDATED_CHAR);
            d->state = UNCHANGED;
        }
    }

    /* Update display */
    if (show_details)
    {
        update_details(screen, show_details);
        show_panel(screen->details_panel);
    }
    else
      hide_panel(screen->details_panel);

    update_panels_safe();
}

/* Capture user input (keys) and timeout to periodically referesh */
static void process(screen_t *screen)
{
    int c;

    /* Force initial drawing */
    show_details = NULL;
    while ((c = getch()) != 'Q' && c != 'q')
    {
        switch (c)
        {
            case KEY_UP:
            case 'k':
              menu_driver_update(screen, REQ_UP_ITEM);
              break;

            case KEY_DOWN:
            case 'j':
              menu_driver_update(screen, REQ_DOWN_ITEM);
              break;

            case KEY_ENTER:
            case '\n':
            case 'l':
#ifdef HAVE_KQUEUE
              /* We send a signal to ourself to wakeup the kevent routine */
              kill(getpid(), SIGUSR1);
#else /* !HAVE_KQUEUE */
              show_details = item_userptr(current_item(screen->menu));
#endif /* HAVE_KQUEUE */

              break;

            /*  If no key was registered, or on some wacky
             * input we don't care about don't modify the screen state.
             */
            case ERR:
              break;

            /* Someother key was pressed, exit details window */
            default:
#ifdef HAVE_KQUEUE
              kill(getpid(), SIGUSR2);
#else /* !HAVE_KQUEUE */
              show_details = NULL;
#endif
        }
    }
}


int main(int argc, char **argv)
{
    int i, timeout_secs, opened_files = 0;
    screen_t *screen;
    data_t *datas;
    pthread_t *thread;
    const char *fname;
    struct sigaction action;

    /* Args */
    fname = 0;
    timeout_secs = DEFAULT_TIMEOUT_SECS;
    for (i=1; i<argc; ++i)
    {
        if (strncmp(argv[i], "-d", strlen("-d")) == 0)
        {
            if (i+1 < argc)
              timeout_secs = atoi(argv[++i]);
            else
              usage(argv[0], "Incorrect timeout value specified");
        }
        else if (strncmp(argv[i], "-h", strlen("-h")) == 0)
          usage(argv[0], NULL);
        else if (argv[i][0] != '-')
          fname = argv[i];
        else
          usage(argv[0], "Invalid argument specified");
    }

    /* Sanity check args */
    if (!fname)
      usage(argv[0], "Please provide a configuration file");
    if (timeout_secs < 0)
      usage(argv[0], "Incorrect timeout value specified");

    DBG("Using config:  %s", fname);
    DBG("Using timeout: %d seconds", timeout_secs);

    /* Disabling SIGUSR1 */
    action.sa_handler = SIG_IGN;
    sigaction(SIGUSR1, &action, NULL);
    sigaction(SIGUSR2, &action, NULL);

    /* Load data */
    datas = data_init(fname, &opened_files);

    /* Initialize display */
    screen = screen_create(datas, timeout_secs * 1000);

    /* Initialize columns variable */
    columns = COLS;

    /* Create reading threads */
    thread = threads_init(opened_files, screen);

    /* Do the work */
    process(screen);

    /* Cleanup */
    threads_destroy(thread);
    data_destroy(screen->datas);
    screen_destroy(screen);

    return 0;
}
