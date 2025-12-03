#ifdef _WIN32
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <io.h>
#include <tchar.h>
#include <shlwapi.h>
#pragma comment(lib, "Shlwapi.lib")
#else
#define _XOPEN_SOURCE 700
#include <pthread.h>
#include <dirent.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fnmatch.h>
#include <regex.h>
#include <errno.h>
#endif

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <ctype.h>

#ifdef __APPLE__
#include <sys/types.h>
#include <sys/sysctl.h>
#endif

#ifndef PATH_MAX
#define PATH_MAX 4096
#endif

#ifndef FNM_CASEFOLD
#define FNM_CASEFOLD 0x01
#endif

#ifdef _WIN32
#define COLOR_RED ""
#define COLOR_YELLOW ""
#define COLOR_RESET ""
#else
#define COLOR_RED "\x1b[31m"
#define COLOR_YELLOW "\x1b[33m"
#define COLOR_RESET "\x1b[0m"
#endif

typedef struct Task {
    char *Path;
    struct Task *Next;
} Task;

typedef struct {
#ifdef _WIN32
    CRITICAL_SECTION Cs;
    CONDITION_VARIABLE Cv;
#else
    pthread_mutex_t M;
    pthread_cond_t Cv;
#endif
    Task *Head;
    Task *Tail;
    int Closed;
    long long Size;
} TaskQueue;

static TaskQueue Queue;
static volatile long long VisitedCount = 0;
static volatile long long FoundCount = 0;

static int MaxDepth = -1;
static int IgnoreCase = 0;
static int FollowSymlinks = 0;
static int ShowProgress = 0;
static int UseGlob = 0;
static int UseRegex = 0;
static int SearchForDirectories = 0;

static uint64_t MaxFileSize = 0;
static uint64_t MinFileSize = 0;

static char *Pattern = NULL;
static char **Patterns = NULL;
static int PatternCount = 0;

static char *StartPath = NULL;
static int ThreadCount = 0;
static char **Excludes = NULL;
static int ExcludeCount = 0;
static int AdminRequired = 1;

#ifndef _WIN32
static regex_t CompiledRx;
static int RxCompiled = 0;
static regex_t *CompiledList = NULL;
#endif

static char *XStrdup(const char *S){
#ifdef _WIN32
    return _strdup(S);
#else
    return strdup(S);
#endif
}

#ifdef _WIN32
#define AtomicInc64(Ptr) InterlockedIncrement64((volatile LONG64*)(Ptr))
#define AtomicDec64(Ptr) InterlockedDecrement64((volatile LONG64*)(Ptr))
#define AtomicGet64(Ptr) InterlockedCompareExchange64((volatile LONG64*)(Ptr), 0, 0)
#else
static inline long long AtomicInc64(volatile long long *Ptr){
    return __atomic_add_fetch(Ptr, 1, __ATOMIC_RELAXED);
}
static inline long long AtomicDec64(volatile long long *Ptr){
    return __atomic_sub_fetch(Ptr, 1, __ATOMIC_RELAXED);
}
static inline long long AtomicGet64(volatile long long *Ptr){
    long long V;
    __atomic_load(Ptr, &V, __ATOMIC_RELAXED);
    return V;
}
#endif

static void TqInit(TaskQueue *Q){
    Q->Head = Q->Tail = NULL;
    Q->Closed = 0;
    Q->Size = 0;
#ifdef _WIN32
    InitializeCriticalSection(&Q->Cs);
    InitializeConditionVariable(&Q->Cv);
#else
    pthread_mutex_init(&Q->M, NULL);
    pthread_cond_init(&Q->Cv, NULL);
#endif
}

static void TqPush(TaskQueue *Q, const char *Path){
    Task *T = (Task*)malloc(sizeof(Task));
    if(!T) return;
    T->Path = XStrdup(Path);
    T->Next = NULL;
#ifdef _WIN32
    EnterCriticalSection(&Q->Cs);
    if(Q->Tail) Q->Tail->Next = T; else Q->Head = T;
    Q->Tail = T;
    Q->Size++;
    WakeConditionVariable(&Q->Cv);
    LeaveCriticalSection(&Q->Cs);
#else
    pthread_mutex_lock(&Q->M);
    if(Q->Tail) Q->Tail->Next = T; else Q->Head = T;
    Q->Tail = T;
    Q->Size++;
    pthread_cond_signal(&Q->Cv);
    pthread_mutex_unlock(&Q->M);
#endif
}

static char *TqPop(TaskQueue *Q){
#ifdef _WIN32
    EnterCriticalSection(&Q->Cs);
    while(Q->Head == NULL && !Q->Closed)
        SleepConditionVariableCS(&Q->Cv, &Q->Cs, INFINITE);
    if(!Q->Head){
        LeaveCriticalSection(&Q->Cs);
        return NULL;
    }
    Task *T = Q->Head;
    Q->Head = T->Next;
    if(!Q->Head) Q->Tail = NULL;
    Q->Size--;
    LeaveCriticalSection(&Q->Cs);
#else
    pthread_mutex_lock(&Q->M);
    while(Q->Head == NULL && !Q->Closed)
        pthread_cond_wait(&Q->Cv, &Q->M);
    if(!Q->Head){
        pthread_mutex_unlock(&Q->M);
        return NULL;
    }
    Task *T = Q->Head;
    Q->Head = T->Next;
    if(!Q->Head) Q->Tail = NULL;
    Q->Size--;
    pthread_mutex_unlock(&Q->M);
#endif
    char *P = T->Path;
    free(T);
    return P;
}

static void TqClose(TaskQueue *Q){
#ifdef _WIN32
    EnterCriticalSection(&Q->Cs);
    Q->Closed = 1;
    WakeAllConditionVariable(&Q->Cv);
    LeaveCriticalSection(&Q->Cs);
#else
    pthread_mutex_lock(&Q->M);
    Q->Closed = 1;
    pthread_cond_broadcast(&Q->Cv);
    pthread_mutex_unlock(&Q->M);
#endif
}

static int IsAdmin(){
#ifdef _WIN32
    BOOL IsAdmin = FALSE;
    PSID AdminGroup = NULL;
    SID_IDENTIFIER_AUTHORITY NtAuth = SECURITY_NT_AUTHORITY;
    if(AllocateAndInitializeSid(&NtAuth, 2, SECURITY_BUILTIN_DOMAIN_RID,
                                 DOMAIN_ALIAS_RID_ADMINS, 0,0,0,0,0,0,
                                 &AdminGroup)){
        CheckTokenMembership(NULL, AdminGroup, &IsAdmin);
        FreeSid(AdminGroup);
    }
    return IsAdmin;
#else
    return geteuid() == 0;
#endif
}

static int PathIsExcluded(const char *P){
    for(int I=0;I<ExcludeCount;I++){
        size_t L = strlen(Excludes[I]);
        if(L && strncmp(P, Excludes[I], L)==0) return 1;
    }
    return 0;
}

static void AddExclude(const char *P){
    char **Tmp = (char**)realloc(Excludes, sizeof(char*) * (ExcludeCount + 1));
    if(!Tmp) return;
    Excludes = Tmp;
    Excludes[ExcludeCount++] = XStrdup(P);
}

static void AddPatternToList(const char *Pat){
    char **Tmp = (char**)realloc(Patterns, sizeof(char*) * (PatternCount + 1));
    if(!Tmp) return;
    Patterns = Tmp;
    Patterns[PatternCount++] = XStrdup(Pat);
}

static void ParsePatternList(const char *Arg){
    char *Buf = XStrdup(Arg);
    if(!Buf) return;

    char *P = Buf;
    size_t Len = strlen(Buf);

    if(Len > 0 && Buf[0] == '['){
        P++;
        if(Len > 1 && Buf[Len-1] == ']'){
            Buf[Len-1] = '\0';
        }
    }

    char *Token = strtok(P, ",");
    while(Token){
        while(isspace((unsigned char)*Token)) Token++;
        char *End = Token + strlen(Token) - 1;
        while(End >= Token && isspace((unsigned char)*End)){
            *End = '\0';
            End--;
        }
        if(*Token){
            AddPatternToList(Token);
        }
        Token = strtok(NULL, ",");
    }

    free(Buf);
}

#ifndef _WIN32
static int SingleMatchPosix(const char *Name, const char *Pat, regex_t *RxOpt){
    if(UseRegex && RxOpt)
        return regexec(RxOpt, Name, 0, NULL, 0) == 0;

    if(UseGlob)
        return fnmatch(Pat, Name, IgnoreCase ? FNM_CASEFOLD : 0) == 0;

    if(IgnoreCase){
        while(*Name && *Pat){
            if(tolower((unsigned char)*Name) != tolower((unsigned char)*Pat))
                return 0;
            Name++;
            Pat++;
        }
        return *Pat == '\0' && *Name == '\0';
    }

    return strcmp(Name, Pat) == 0;
}

static int NameMatches(const char *Name){
    if(PatternCount > 0){
        for(int I = 0; I < PatternCount; I++){
            regex_t *RxOpt = NULL;
            if(UseRegex && CompiledList && I < PatternCount){
                RxOpt = &CompiledList[I];
            }
            if(SingleMatchPosix(Name, Patterns[I], RxOpt))
                return 1;
        }
        return 0;
    }

    if(Pattern){
        regex_t *RxOpt = RxCompiled ? &CompiledRx : NULL;
        return SingleMatchPosix(Name, Pattern, RxOpt);
    }

    return 0;
}
#else
static int SingleMatchWin(const char *Name, const char *Pat){
    if(UseGlob){
        DWORD Flags = IgnoreCase ? 0 : PMSF_NORMAL;
        return PathMatchSpecExA(Name, Pat, Flags) == S_OK;
    }

    if(IgnoreCase)
        return _stricmp(Name, Pat) == 0;

    return strcmp(Name, Pat) == 0;
}

static int NameMatches(const char *Name){
    if(PatternCount > 0){
        for(int I = 0; I < PatternCount; I++){
            if(SingleMatchWin(Name, Patterns[I]))
                return 1;
        }
        return 0;
    }

    if(Pattern)
        return SingleMatchWin(Name, Pattern);

    return 0;
}
#endif

static void MaybePrintProgress(){
    if(!ShowProgress) return;
    long long V = AtomicGet64(&VisitedCount);
    if(V % 1000 == 0){
        long long F = AtomicGet64(&FoundCount);
        long long QSize = Queue.Size;
        fprintf(stderr, "\r[Visited: %lld | Found: %lld | Queue: %lld] ", V, F, QSize);
        fflush(stderr);
    }
}

#ifndef _WIN32
static void LogError(const char *Path, const char *Reason){
    fprintf(stderr, COLOR_RED "[ERROR]" COLOR_RESET " Failed to process %s: %s\n", Path, Reason);
    fflush(stderr);
}

static void ProcessDir(const char *DirPath){
    DIR *D = opendir(DirPath);
    if(!D) {
        LogError(DirPath, strerror(errno));
        return;
    }

    struct dirent *E;
    char Full[PATH_MAX];
    struct stat St;

    while((E = readdir(D))){
        if(!strcmp(E->d_name,".") || !strcmp(E->d_name,"..")) continue;
        if(snprintf(Full, sizeof(Full), "%s/%s", DirPath, E->d_name) >= (int)sizeof(Full)) continue;
        if(PathIsExcluded(Full)) continue;

        AtomicInc64(&VisitedCount);
        MaybePrintProgress();

        if((FollowSymlinks ? stat(Full,&St) : lstat(Full,&St)) != 0) {
            LogError(Full, strerror(errno));
            continue;
        }

        int IsDir = S_ISDIR(St.st_mode);
        int ShouldMatch = !IsDir || SearchForDirectories;
        int IsMatch = 0;

        if(!IsDir){
            uint64_t FileSize = St.st_size;
            if(MaxFileSize > 0 && FileSize > MaxFileSize) continue;
            if(MinFileSize > 0 && FileSize < MinFileSize) continue;
        }

        if(ShouldMatch && NameMatches(E->d_name)){
            IsMatch = 1;
        }

        if(IsMatch){
            AtomicInc64(&FoundCount);
            printf("%s\n", Full);
            fflush(stdout);
        }

        if(IsDir){
            TqPush(&Queue, Full);
        }
    }

    closedir(D);
}
#else
static void LogError(const char *Path, const char *Reason){
    fprintf(stderr, "[ERROR] Failed to process %s: %s\n", Path, Reason);
    fflush(stderr);
}

static void ProcessDir(const char *DirPath){
    char Pat[MAX_PATH];
    size_t Len = strlen(DirPath);
    if(Len + 3 >= sizeof(Pat)) return;

    snprintf(Pat, sizeof(Pat), "%s\\*", DirPath);

    WIN32_FIND_DATAA Fd;
    HANDLE H = FindFirstFileA(Pat, &Fd);
    if(H == INVALID_HANDLE_VALUE){
        LogError(DirPath, "Access Denied or Not Found");
        return;
    }

    do {
        if(strcmp(Fd.cFileName,".")==0 || strcmp(Fd.cFileName,"..")==0) continue;

        char Full[MAX_PATH];
        if(Len + strlen(Fd.cFileName) + 2 >= sizeof(Full)) continue;

        snprintf(Full, sizeof(Full), "%s\\%s", DirPath, Fd.cFileName);
        if(PathIsExcluded(Full)) continue;

        AtomicInc64(&VisitedCount);
        MaybePrintProgress();

        int IsDir = Fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY;
        int ShouldMatch = !IsDir || SearchForDirectories;
        int IsMatch = 0;

        if(!IsDir){
            uint64_t FileSize = (uint64_t)Fd.nFileSizeHigh << 32 | Fd.nFileSizeLow;
            if(MaxFileSize > 0 && FileSize > MaxFileSize) continue;
            if(MinFileSize > 0 && FileSize < MinFileSize) continue;
        }

        if(ShouldMatch && NameMatches(Fd.cFileName)){
            IsMatch = 1;
        }

        if(IsMatch){
            AtomicInc64(&FoundCount);
            printf("%s\n", Full);
            fflush(stdout);
        }

        if(IsDir){
            TqPush(&Queue, Full);
        }
    } while(FindNextFileA(H, &Fd));

    FindClose(H);
}
#endif

#ifdef _WIN32
DWORD WINAPI Worker(LPVOID A){
    (void)A;
    for(;;){
        char *P = TqPop(&Queue);
        if(!P) break;
        ProcessDir(P);
        free(P);
    }
    return 0;
}
#else
void *Worker(void *A){
    (void)A;
    for(;;){
        char *P = TqPop(&Queue);
        if(!P) break;
        ProcessDir(P);
        free(P);
    }
    return NULL;
}
#endif

static void Usage(const char *N){
    fprintf(stderr,
        COLOR_YELLOW "Usage: %s -fn <name> | -ms \"[name1, name2]\" [options]\n" COLOR_RESET
        "Options:\n"
        "  -fn <name>                 : Single file/pattern name\n"
        "  -ms, --multiple-search LST : Comma-separated list of names\n"
        "  -p <path>                  : Starting path (default: root)\n"
        "  -t <threads>               : Number of threads\n"
        "  --glob                     : Glob matching (fnmatch / PathMatchSpec)\n"
        "  --regex                    : Regex matching (POSIX only)\n"
        "  --ignore-case              : Case-insensitive matching\n"
        "  --follow-symlinks          : Follow symlinks (POSIX)\n"
        "  --dir                      : Search for directories as well as files (default: files only)\n"
        "  --max-size <bytes>         : Maximum file size to include in search (bytes)\n"
        "  --min-size <bytes>         : Minimum file size to include in search (bytes)\n"
        "  --exclude <path>, -x <path>: Do not scan this path prefix\n"
        "  --progress                 : Show visited/found count progress\n"
        "  --no-admin-check           : Disable root/Administrator check\n"
        "\n", N);
}

int main(int Argc, char **Argv){
#ifdef _WIN32
    {
        SYSTEM_INFO Si;
        GetSystemInfo(&Si);
        if(Si.dwNumberOfProcessors > 0)
            ThreadCount = (int)Si.dwNumberOfProcessors;
        else
            ThreadCount = 4;
    }
#else
    {
        int Nc = 4;
    #ifdef __APPLE__
        size_t Size = sizeof(Nc);
        if(sysctlbyname("hw.ncpu", &Nc, &Size, NULL, 0) != 0) Nc = 4;
    #else
        long Ln = sysconf(_SC_NPROCESSORS_ONLN);
        if(Ln > 0) Nc = (int)Ln;
    #endif
        ThreadCount = Nc;
    }
#endif

    for(int I=1;I<Argc;I++){
        if(!strcmp(Argv[I],"-p") && I+1<Argc){
            StartPath = Argv[++I];
        } else if(!strcmp(Argv[I],"-fn") && I+1<Argc){
            Pattern = Argv[++I];
        } else if((!strcmp(Argv[I],"-ms") || !strcmp(Argv[I],"--multiple-search")) && I+1<Argc){
            ParsePatternList(Argv[++I]);
        } else if(!strcmp(Argv[I],"--ignore-case")){
            IgnoreCase = 1;
        } else if(!strcmp(Argv[I],"--glob")){
            UseGlob = 1;
        } else if(!strcmp(Argv[I],"--regex")){
            UseRegex = 1;
        } else if(!strcmp(Argv[I],"--progress")){
            ShowProgress = 1;
        } else if(!strcmp(Argv[I],"--follow-symlinks")){
            FollowSymlinks = 1;
        } else if(!strcmp(Argv[I],"--dir")){
            SearchForDirectories = 1;
        } else if(!strcmp(Argv[I],"--max-size") && I+1<Argc){
            MaxFileSize = strtoull(Argv[++I], NULL, 10);
        } else if(!strcmp(Argv[I],"--min-size") && I+1<Argc){
            MinFileSize = strtoull(Argv[++I], NULL, 10);
        } else if((!strcmp(Argv[I],"-x") || !strcmp(Argv[I],"--exclude")) && I+1<Argc){
            AddExclude(Argv[++I]);
        } else if(!strcmp(Argv[I],"-t") && I+1<Argc){
            ThreadCount = atoi(Argv[++I]);
        } else if(!strcmp(Argv[I],"--no-admin-check")){
            AdminRequired = 0;
        }
    }

    if(ThreadCount < 1)
        ThreadCount = 1;

    if(!Pattern && PatternCount == 0){
        Usage(Argv[0]);
        return 1;
    }

    if(!StartPath){
#ifdef _WIN32
        StartPath = "C:\\";
#else
        StartPath = "/";
#endif
    }

    if(AdminRequired && !IsAdmin()){
        fprintf(stderr, COLOR_RED "[ERROR]" COLOR_RESET " Run as Administrator/root (or disable with --no-admin-check)\n");
        return 1;
    }

#ifndef _WIN32
    if(UseRegex){
        int Flags = REG_EXTENDED | (IgnoreCase ? REG_ICASE : 0);

        if(Pattern){
            if(regcomp(&CompiledRx, Pattern, Flags)){
                fprintf(stderr, COLOR_RED "[ERROR]" COLOR_RESET " Invalid regex: %s\n", Pattern);
                return 1;
            }
            RxCompiled = 1;
        }

        if(PatternCount > 0){
            CompiledList = (regex_t*)malloc(sizeof(regex_t) * PatternCount);
            if(!CompiledList){
                fprintf(stderr, COLOR_RED "[ERROR]" COLOR_RESET " Out of memory for regex list\n");
                return 1;
            }
            for(int I = 0; I < PatternCount; I++){
                if(regcomp(&CompiledList[I], Patterns[I], Flags)){
                    fprintf(stderr, COLOR_RED "[ERROR]" COLOR_RESET " Invalid regex in list: %s\n", Patterns[I]);
                    return 1;
                }
            }
        }
    }
#endif

    TqInit(&Queue);
    TqPush(&Queue, StartPath);

#ifdef _WIN32
    HANDLE *Th = (HANDLE*)malloc(sizeof(HANDLE)*ThreadCount);
    if(!Th){
        fprintf(stderr, COLOR_RED "[ERROR]" COLOR_RESET " Thread alloc failed\n");
        return 1;
    }
    for(int I=0;I<ThreadCount;I++){
        Th[I] = CreateThread(NULL,0,Worker,NULL,0,NULL);
        if(!Th[I]){
            fprintf(stderr, COLOR_RED "[ERROR]" COLOR_RESET " CreateThread failed\n");
            return 1;
        }
    }

    TqClose(&Queue);

    WaitForMultipleObjects(ThreadCount, Th, TRUE, INFINITE);
    for(int I=0;I<ThreadCount;I++) CloseHandle(Th[I]);
    free(Th);
#else
    pthread_t *Th = (pthread_t*)malloc(sizeof(pthread_t)*ThreadCount);
    if(!Th){
        fprintf(stderr, COLOR_RED "[ERROR]" COLOR_RESET " Thread alloc failed\n");
        return 1;
    }

    for(int I=0;I<ThreadCount;I++){
        if(pthread_create(&Th[I],NULL,Worker,NULL) != 0){
            fprintf(stderr, COLOR_RED "[ERROR]" COLOR_RESET " pthread_create failed\n");
            return 1;
        }
    }

    TqClose(&Queue);

    for(int I=0;I<ThreadCount;I++){
        pthread_join(Th[I],NULL);
    }
    free(Th);
#endif

    if(ShowProgress){
        fprintf(stderr, "\r%60s\r", "");
        fprintf(stderr, "\n");
    }

    printf(COLOR_YELLOW "\nDone." COLOR_RESET " Visited=%lld Found=%lld\n",
            AtomicGet64(&VisitedCount),
            AtomicGet64(&FoundCount));

#ifndef _WIN32
    if(RxCompiled)
        regfree(&CompiledRx);
    if(CompiledList){
        for(int I=0;I<PatternCount;I++){
            regfree(&CompiledList[I]);
        }
        free(CompiledList);
    }
#endif

    return 0;
}
