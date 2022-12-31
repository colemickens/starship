use once_cell::sync::OnceCell;
use regex::Regex;

use super::{Context, Module, RootModuleConfig};

use crate::configs::gitstatusd::GitstatusdConfig;
use crate::formatter::StringFormatter;
use crate::segment::Segment;
use std::ffi::OsStr;
use std::sync::Arc;
use std::{process, io, path, fmt};

const MODULE_NAME: &str = "gitstatusd";

const ALL_STATUS_FORMAT: &str = "$conflicted$stashed$deleted$renamed$modified$staged$untracked";

/// Creates a module with the Git branch in the current directory
///
/// Will display the branch name if the current directory is a git repo
/// By default, the following symbols will be used to represent the repo's status:
///   - `=` – This branch has merge conflicts
///   - `⇡` – This branch is ahead of the branch being tracked
///   - `⇣` – This branch is behind of the branch being tracked
///   - `⇕` – This branch has diverged from the branch being tracked
///   - `` – This branch is up-to-date with the branch being tracked
///   - `?` — There are untracked files in the working directory
///   - `$` — A stash exists for the local repository
///   - `!` — There are file modifications in the working directory
///   - `+` — A new file has been added to the staging area
///   - `»` — A renamed file has been added to the staging area
///   - `✘` — A file's deletion has been added to the staging area
pub fn module<'a>(context: &'a Context) -> Option<Module<'a>> {
    let mut module = context.new_module(MODULE_NAME);
    let config: GitstatusdConfig = GitstatusdConfig::try_load(module.config);

    let info = Arc::new(GitstatusdInfo::load(context, config.clone()));

    //Return None if not in git repository
    context.get_repo().ok()?;

    let parsed = StringFormatter::new(config.format).and_then(|formatter| {
        formatter
            .map_meta(|variable, _| match variable {
                "all_status" => Some(ALL_STATUS_FORMAT),
                _ => None,
            })
            .map_style(|variable: &str| match variable {
                "style" => Some(Ok(config.style)),
                _ => None,
            })
            .map_variables_to_segments(|variable: &str| {
                let info = Arc::clone(&info);
                let segments = match variable {
                    "stashed" => info.get_stashed().and_then(|count| {
                        format_count(config.stashed, "git_status.stashed", context, count)
                    }),
                    "ahead_behind" => info.get_ahead_behind().and_then(|(ahead, behind)| {
                        let (ahead, behind) = (ahead?, behind?);
                        if ahead > 0 && behind > 0 {
                            format_text(
                                config.diverged,
                                "git_status.diverged",
                                context,
                                |variable| match variable {
                                    "ahead_count" => Some(ahead.to_string()),
                                    "behind_count" => Some(behind.to_string()),
                                    _ => None,
                                },
                            )
                        } else if ahead > 0 && behind == 0 {
                            format_count(config.ahead, "git_status.ahead", context, ahead)
                        } else if behind > 0 && ahead == 0 {
                            format_count(config.behind, "git_status.behind", context, behind)
                        } else {
                            format_symbol(config.up_to_date, "git_status.up_to_date", context)
                        }
                    }),
                    "conflicted" => info.get_conflicted().and_then(|count| {
                        format_count(config.conflicted, "git_status.conflicted", context, count)
                    }),
                    "deleted" => info.get_deleted().and_then(|count| {
                        format_count(config.deleted, "git_status.deleted", context, count)
                    }),
                    "renamed" => info.get_renamed().and_then(|count| {
                        format_count(config.renamed, "git_status.renamed", context, count)
                    }),
                    "modified" => info.get_modified().and_then(|count| {
                        format_count(config.modified, "git_status.modified", context, count)
                    }),
                    "staged" => info.get_staged().and_then(|count| {
                        format_count(config.staged, "git_status.staged", context, count)
                    }),
                    "untracked" => info.get_untracked().and_then(|count| {
                        format_count(config.untracked, "git_status.untracked", context, count)
                    }),
                    _ => None,
                };
                segments.map(Ok)
            })
            .parse(None, Some(context))
    });

    module.set_segments(match parsed {
        Ok(segments) => {
            if segments.is_empty() {
                return None;
            } else {
                segments
            }
        }
        Err(error) => {
            log::warn!("Error in module `git_status`:\n{}", error);
            return None;
        }
    });

    Some(module)
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// GITSTATUSD
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
#[derive(Debug, PartialEq)]
/// An error if the responce from gitstatusd couldn't be parsed
pub enum ResponceParseError {
    /// Not Enought Parts were recieved
    TooShort,
    /// A part was sent, but we cant parse it.
    InvalidPart,
    ParseIntError(std::num::ParseIntError),
}

impl From<std::num::ParseIntError> for ResponceParseError {
    fn from(e: std::num::ParseIntError) -> Self {
        Self::ParseIntError(e)
    }
}

macro_rules! munch {
    ($expr:expr) => {
        match $expr.next() {
            Some(v) => v,
            None => return Err($crate::modules::gitstatusd::ResponceParseError::TooShort),
        }
    };
}

impl std::str::FromStr for GitStatus {
    type Err = ResponceParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        GitStatus::from_str(s)
    }
}

impl GitStatus {
    // TODO: Make this run on &[u8]
    fn from_str(s: &str) -> Result<Self, ResponceParseError> {
        let mut parts = s.split("\x1f");
        let id = munch!(parts);
        let is_repo = munch!(parts);
        match is_repo {
            "0" => {
                return Ok(GitStatus {
                    id: id.to_owned(),
                    details: Option::None,
                })
            }
            // 1 indicated a git repo, so we do the real stuff
            "1" => {}
            // If not 0 or 1, give up
            _ => return Err(ResponceParseError::InvalidPart),
        }

        let abspath = munch!(parts);
        let head_commit_hash = munch!(parts);
        let local_branch = munch!(parts);
        let upstream_branch = munch!(parts);
        let remote_name = munch!(parts);
        let remote_url = munch!(parts);
        let repository_state = munch!(parts);

        let num_files_in_index: u32 = munch!(parts).parse()?;
        let num_staged_changes: u32 = munch!(parts).parse()?;
        let num_unstaged_changes: u32 = munch!(parts).parse()?;
        let num_conflicted_changes: u32 = munch!(parts).parse()?;
        let num_untrached_files: u32 = munch!(parts).parse()?;
        let commits_ahead: u32 = munch!(parts).parse()?;
        let commits_behind: u32 = munch!(parts).parse()?;
        let num_stashes: u32 = munch!(parts).parse()?;
        let last_tag = munch!(parts);
        let num_unstaged_deleted: u32 = munch!(parts).parse()?;
        let num_staged_new: u32 = munch!(parts).parse()?;
        let num_staged_deleted: u32 = munch!(parts).parse()?;
        let push_remote_name = munch!(parts);
        let push_remote_url: &str = munch!(parts);
        let commits_ahead_push_remote: u32 = munch!(parts).parse()?;
        let commits_behind_push_remote: u32 = munch!(parts).parse()?;
        let num_index_skip_worktree: u32 = munch!(parts).parse()?;
        let num_index_assume_unchanged: u32 = munch!(parts).parse()?;

        // Only do ownership once we have all the stuff
        let git_part = GitDetails {
            abspath: abspath.to_owned(),
            head_commit_hash: head_commit_hash.to_owned(),
            local_branch: local_branch.to_owned(),
            upstream_branch: upstream_branch.to_owned(),
            remote_name: remote_name.to_owned(),
            remote_url: remote_url.to_owned(),
            repository_state: repository_state.to_owned(),
            num_files_in_index,
            num_staged_changes,
            num_unstaged_changes,
            num_conflicted_changes,
            num_untrached_files,
            commits_ahead,
            commits_behind,
            num_stashes,
            last_tag: last_tag.to_owned(),
            num_unstaged_deleted,
            num_staged_new,
            num_staged_deleted,
            push_remote_name: push_remote_name.to_owned(),
            push_remote_url: push_remote_url.to_owned(),
            commits_ahead_push_remote,
            commits_behind_push_remote,
            num_index_skip_worktree,
            num_index_assume_unchanged,
        };

        Ok(GitStatus {
            id: id.to_owned(),
            details: Option::Some(git_part),
        })
    }
}


struct GitStatusDaemon {
    // I need to store the child so it's pipes don't close
    _proc: process::Child,
    stdin: process::ChildStdin,
    stdout: io::BufReader<process::ChildStdout>,
    // TODO: decide if I need this
    _stderr: process::ChildStderr,
}

struct GitstatusdInfo<'a> {
    config: GitstatusdConfig<'a>,
    context: &'a Context<'a>,
    repo_status: OnceCell<Option<GitDetails>>,
}

#[derive(Copy, Clone, Debug, Hash)]
/// Tell gitstatusd weather or not to read the git index
pub enum ReadIndex {
    /// default behavior of computing everything
    ReadAll = 0,
    /// Disables computation of anything that requires reading git index
    DontRead = 1,
}

/// A Request to be sent to the demon.
pub struct StatusRequest {
    // TODO: Are these always utf-8
    // TODO: borrow these
    /// The request Id, can be blank
    pub id: String,
    /// Path to the directory for which git stats are being requested.
    ///
    /// If the first character is ':', it is removed and the remaning path is
    /// treated as GIT_DIR.
    pub dir: String,
    /// Wether or not to read the git index
    pub read_index: ReadIndex,
}

// TODO, this should probably work for non utf8.
impl fmt::Display for StatusRequest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{id}\x1f{dir}\x1f{index}\x1e",
            id = self.id,
            dir = self.dir,
            index = self.read_index as u8
        )
    }
}

impl GitStatusDaemon {
    // TODO: does the path matter
    // TODO: binary detection
    /// Create a new status demon.
    ///
    /// - `bin_path`: The path to the `gitstatusd` binary.
    /// - `run_dir`: The directory to run the binary in.
    pub fn new<C: AsRef<OsStr> + Default, P: AsRef<path::Path>>(
        bin_path: C,
        run_dir: P,
    ) -> io::Result<GitStatusDaemon> {
        let mut proc = process::Command::new(bin_path)
            .current_dir(run_dir)
            .stdin(process::Stdio::piped())
            .stdout(process::Stdio::piped())
            .stderr(process::Stdio::piped())
            .spawn()?;

        let stdin = proc.stdin.take().ok_or(io::Error::new(
            io::ErrorKind::BrokenPipe,
            "Couldn't obtain stdin",
        ))?;
        let stdout = io::BufReader::new(proc.stdout.take().ok_or(
            io::Error::new(io::ErrorKind::BrokenPipe, "Couldn't obtain stdout"),
        )?);
        let stderr = proc.stderr.take().ok_or(io::Error::new(
            io::ErrorKind::BrokenPipe,
            "Couldn't obtain stderr",
        ))?;

        Ok(GitStatusDaemon {
            _proc: proc,
            stdin,
            stdout,
            _stderr: stderr,
        })
    }

    //TODO: Better Error Handling
    //TODO: Non blocking version
    //TODO: Id generation
    /// Get the git status
    pub fn request(&mut self, r: StatusRequest) -> io::Result<GitStatus> {

        let mut file = File::open(self.pidfile)?;
        let mut string = String::new();
        let pid = file.read_to_string(&mut string)?;

        // connect to pid with procfs?

        println!("{:?}", pid);
        let status = GitStatus::Default();
        Ok(status)
    }
}


#[derive(Debug, PartialEq)]
/// The result of a request for the git status.
///
/// If the request was inside a git reposity, `details` will contain a
/// `GitDetails` with the results
pub struct GitStatus {
    /// Request id. The same as the first field in the request.
    pub id: String,
    /// The inner responce.
    pub details: Option<GitDetails>,
}



/// Details about git state.
///
/// Note: Renamed files are reported as deleted plus new.
#[derive(Debug, PartialEq)]
pub struct GitDetails {
    /// Absolute path to the git repository workdir.
    pub abspath: String,
    /// Commit hash that HEAD is pointing to. 40 hex digits.
    // TODO: Change the type
    pub head_commit_hash: String,
    // TODO: Docs unclear
    /// Local branch name or empty if not on a branch.
    pub local_branch: String,
    /// Upstream branch name. Can be empty.
    pub upstream_branch: String,
    /// The remote name, e.g. "upstream" or "origin".
    pub remote_name: String,
    /// Remote URL. Can be empty.
    pub remote_url: String,
    /// Repository state, A.K.A. action. Can be empty.
    pub repository_state: String,
    /// The number of files in the index.
    pub num_files_in_index: u32,
    /// The number of staged changes.
    pub num_staged_changes: u32,
    /// The number of unstaged changes.
    pub num_unstaged_changes: u32,
    /// The number of conflicted changes.
    pub num_conflicted_changes: u32,
    /// The number of untracked files.
    pub num_untrached_files: u32,
    /// Number of commits the current branch is ahead of upstream.
    pub commits_ahead: u32,
    /// Number of commits the current branch is behind upstream.
    pub commits_behind: u32,
    /// The number of stashes.
    pub num_stashes: u32,
    /// The last tag (in lexicographical order) that points to the same
    /// commit as HEAD.
    pub last_tag: String,
    /// The number of unstaged deleted files.
    pub num_unstaged_deleted: u32,
    /// The number of staged new files.
    pub num_staged_new: u32,
    /// The number of staged deleted files.
    pub num_staged_deleted: u32,
    /// The push remote name, e.g. "upstream" or "origin".
    pub push_remote_name: String,
    /// Push remote URL. Can be empty.
    pub push_remote_url: String,
    /// Number of commits the current branch is ahead of push remote.
    pub commits_ahead_push_remote: u32,
    /// Number of commits the current branch is behind push remote.
    pub commits_behind_push_remote: u32,
    /// Number of files in the index with skip-worktree bit set.
    pub num_index_skip_worktree: u32,
    /// Number of files in the index with assume-unchanged bit set.
    pub num_index_assume_unchanged: u32,
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// GITSTATUSD (END)
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

// TODO: make the read_index configureable
// TODO: gitstatusd should use osstring? or pathbuf?
impl<'a> GitstatusdInfo<'a> {
    pub fn load(context: &'a Context, config: GitstatusdConfig<'a>) -> Self {
        Self {
            config,
            context,
            repo_status: OnceCell::new(),
        }
    }

    pub fn get_repo_status(&self) -> &Option<GitDetails> {
        let req_id = "???";
        let _gsd = GitStatusDaemon::new(
            "gitstatusd", self.context.runtime_dir);

        match _gsd {
            Ok(gsd) => {
                let req = StatusRequest {
                    id: req_id.to_string(),
                    dir: self.context.logical_dir.to_string_lossy().into_owned(),
                    read_index: ReadIndex::DontRead,
                };
                match gsd.request(req) {
                    Ok(resp) => &resp.details,
                    Err(_) => &None,
                }
            },
            Err(_) => &None,
        }
    }

    pub fn get_ahead_behind(&self) -> Option<(Option<usize>, Option<usize>)> {
        self.get_repo_status().map(|data| (data.ahead, data.behind))
    }

    pub fn get_stashed(&self) -> &Option<usize> {
        self.stashed_count
            .get_or_init(|| match get_stashed_count(self.context) {
                Some(stashed_count) => Some(stashed_count),
                None => {
                    log::debug!("get_stashed_count: git stash execution failed");
                    None
                }
            })
    }

    pub fn get_conflicted(&self) -> Option<usize> {
        self.get_repo_status().map(|data| data.conflicted)
    }

    pub fn get_deleted(&self) -> Option<usize> {
        self.get_repo_status().map(|data| data.deleted)
    }

    pub fn get_renamed(&self) -> Option<usize> {
        self.get_repo_status().map(|data| data.renamed)
    }

    pub fn get_modified(&self) -> Option<usize> {
        self.get_repo_status().map(|data| data.modified)
    }

    pub fn get_staged(&self) -> Option<usize> {
        self.get_repo_status().map(|data| data.staged)
    }

    pub fn get_untracked(&self) -> Option<usize> {
        self.get_repo_status().map(|data| data.untracked)
    }
}

/// Gets the number of files in various git states (staged, modified, deleted, etc...)
fn get_repo_status(context: &Context, config: &GitstatusdConfig) -> Option<RepoStatus> {
    log::debug!("New repo status created");

    let mut repo_status = RepoStatus::default();
    let mut args = vec![
        OsStr::new("-C"),
        context.current_dir.as_os_str(),
        OsStr::new("--no-optional-locks"),
        OsStr::new("status"),
        OsStr::new("--porcelain=2"),
    ];

    // for performance reasons, only pass flags if necessary...
    let has_ahead_behind = !config.ahead.is_empty() || !config.behind.is_empty();
    let has_up_to_date_diverged = !config.up_to_date.is_empty() || !config.diverged.is_empty();
    if has_ahead_behind || has_up_to_date_diverged {
        args.push(OsStr::new("--branch"));
    }

    // ... and add flags that omit information the user doesn't want
    let has_untracked = !config.untracked.is_empty();
    if !has_untracked {
        args.push(OsStr::new("--untracked-files=no"));
    }
    if config.ignore_submodules {
        args.push(OsStr::new("--ignore-submodules=dirty"));
    } else if !has_untracked {
        args.push(OsStr::new("--ignore-submodules=untracked"));
    }

    let status_output = context.exec_cmd("git", &args)?;
    let statuses = status_output.stdout.lines();

    statuses.for_each(|status| {
        if status.starts_with("# branch.ab ") {
            repo_status.set_ahead_behind(status);
        } else if !status.starts_with('#') {
            repo_status.add(status);
        }
    });

    Some(repo_status)
}

fn get_stashed_count(context: &Context) -> Option<usize> {
    let stash_output = context.exec_cmd(
        "git",
        &[
            OsStr::new("-C"),
            context.current_dir.as_os_str(),
            OsStr::new("--no-optional-locks"),
            OsStr::new("stash"),
            OsStr::new("list"),
        ],
    )?;

    Some(stash_output.stdout.trim().lines().count())
}

#[derive(Default, Debug, Copy, Clone)]
struct RepoStatus {
    ahead: Option<usize>,
    behind: Option<usize>,
    conflicted: usize,
    deleted: usize,
    renamed: usize,
    modified: usize,
    staged: usize,
    untracked: usize,
}

impl RepoStatus {
    fn is_deleted(short_status: &str) -> bool {
        // is_wt_deleted || is_index_deleted
        short_status.contains('D')
    }

    fn is_modified(short_status: &str) -> bool {
        // is_wt_modified || is_wt_added
        short_status.ends_with('M') || short_status.ends_with('A')
    }

    fn is_staged(short_status: &str) -> bool {
        // is_index_modified || is_index_added
        short_status.starts_with('M') || short_status.starts_with('A')
    }

    fn parse_normal_status(&mut self, short_status: &str) {
        if Self::is_deleted(short_status) {
            self.deleted += 1;
        }

        if Self::is_modified(short_status) {
            self.modified += 1;
        }

        if Self::is_staged(short_status) {
            self.staged += 1;
        }
    }

    fn add(&mut self, s: &str) {
        match s.chars().next() {
            Some('1') => self.parse_normal_status(&s[2..4]),
            Some('2') => {
                self.renamed += 1;
                self.parse_normal_status(&s[2..4])
            }
            Some('u') => self.conflicted += 1,
            Some('?') => self.untracked += 1,
            Some('!') => (),
            Some(_) => log::error!("Unknown line type in git status output"),
            None => log::error!("Missing line type in git status output"),
        }
    }

    fn set_ahead_behind(&mut self, s: &str) {
        let re = Regex::new(r"branch\.ab \+([0-9]+) \-([0-9]+)").unwrap();

        if let Some(caps) = re.captures(s) {
            self.ahead = caps.get(1).unwrap().as_str().parse::<usize>().ok();
            self.behind = caps.get(2).unwrap().as_str().parse::<usize>().ok();
        }
    }
}

fn format_text<F>(
    format_str: &str,
    config_path: &str,
    context: &Context,
    mapper: F,
) -> Option<Vec<Segment>>
where
    F: Fn(&str) -> Option<String> + Send + Sync,
{
    if let Ok(formatter) = StringFormatter::new(format_str) {
        formatter
            .map(|variable| mapper(variable).map(Ok))
            .parse(None, Some(context))
            .ok()
    } else {
        log::warn!("Error parsing format string `{}`", &config_path);
        None
    }
}

fn format_count(
    format_str: &str,
    config_path: &str,
    context: &Context,
    count: usize,
) -> Option<Vec<Segment>> {
    if count == 0 {
        return None;
    }

    format_text(
        format_str,
        config_path,
        context,
        |variable| match variable {
            "count" => Some(count.to_string()),
            _ => None,
        },
    )
}

fn format_symbol(format_str: &str, config_path: &str, context: &Context) -> Option<Vec<Segment>> {
    format_text(format_str, config_path, context, |_variable| None)
}

#[cfg(test)]
mod tests {
    use ansi_term::{ANSIStrings, Color};
    use std::ffi::OsStr;
    use std::fs::{self, File};
    use std::io::{self, prelude::*};
    use std::path::Path;

    use crate::test::{fixture_repo, FixtureProvider, ModuleRenderer};
    use crate::utils::create_command;

    /// Right after the calls to git the filesystem state may not have finished
    /// updating yet causing some of the tests to fail. These barriers are placed
    /// after each call to git.
    /// This barrier is windows-specific though other operating systems may need it
    /// in the future.
    #[cfg(not(windows))]
    fn barrier() {}
    #[cfg(windows)]
    fn barrier() {
        std::thread::sleep(std::time::Duration::from_millis(500));
    }

    #[allow(clippy::unnecessary_wraps)]
    fn format_output(symbols: &str) -> Option<String> {
        Some(format!(
            "{} ",
            Color::Red.bold().paint(format!("[{}]", symbols))
        ))
    }

    #[test]
    fn show_nothing_on_empty_dir() -> io::Result<()> {
        let repo_dir = tempfile::tempdir()?;

        let actual = ModuleRenderer::new("git_status")
            .path(repo_dir.path())
            .collect();
        let expected = None;

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_behind() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        behind(repo_dir.path())?;

        let actual = ModuleRenderer::new("git_status")
            .path(repo_dir.path())
            .collect();
        let expected = format_output("⇣");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_behind_with_count() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        behind(repo_dir.path())?;

        let actual = ModuleRenderer::new("git_status")
            .config(toml::toml! {
                [git_status]
                behind = "⇣$count"
            })
            .path(repo_dir.path())
            .collect();
        let expected = format_output("⇣1");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_ahead() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        File::create(repo_dir.path().join("readme.md"))?.sync_all()?;
        ahead(repo_dir.path())?;

        let actual = ModuleRenderer::new("git_status")
            .path(&repo_dir.path())
            .collect();
        let expected = format_output("⇡");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_ahead_with_count() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        File::create(repo_dir.path().join("readme.md"))?.sync_all()?;
        ahead(repo_dir.path())?;

        let actual = ModuleRenderer::new("git_status")
            .config(toml::toml! {
                [git_status]
                ahead="⇡$count"
            })
            .path(&repo_dir.path())
            .collect();
        let expected = format_output("⇡1");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_diverged() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        diverge(repo_dir.path())?;

        let actual = ModuleRenderer::new("git_status")
            .path(&repo_dir.path())
            .collect();
        let expected = format_output("⇕");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_diverged_with_count() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        diverge(repo_dir.path())?;

        let actual = ModuleRenderer::new("git_status")
            .config(toml::toml! {
                [git_status]
                diverged=r"⇕⇡$ahead_count⇣$behind_count"
            })
            .path(&repo_dir.path())
            .collect();
        let expected = format_output("⇕⇡1⇣1");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_up_to_date_with_upstream() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        let actual = ModuleRenderer::new("git_status")
            .config(toml::toml! {
                [git_status]
                up_to_date="✓"
            })
            .path(&repo_dir.path())
            .collect();
        let expected = format_output("✓");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_conflicted() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        create_conflict(repo_dir.path())?;

        let actual = ModuleRenderer::new("git_status")
            .path(&repo_dir.path())
            .collect();
        let expected = format_output("=");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_conflicted_with_count() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        create_conflict(repo_dir.path())?;

        let actual = ModuleRenderer::new("git_status")
            .config(toml::toml! {
                [git_status]
                conflicted = "=$count"
            })
            .path(&repo_dir.path())
            .collect();
        let expected = format_output("=1");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_untracked_file() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        create_untracked(repo_dir.path())?;

        let actual = ModuleRenderer::new("git_status")
            .path(&repo_dir.path())
            .collect();
        let expected = format_output("?");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_untracked_file_with_count() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        create_untracked(repo_dir.path())?;

        let actual = ModuleRenderer::new("git_status")
            .config(toml::toml! {
                [git_status]
                untracked = "?$count"
            })
            .path(&repo_dir.path())
            .collect();
        let expected = format_output("?1");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn doesnt_show_untracked_file_if_disabled() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        create_untracked(repo_dir.path())?;

        create_command("git")?
            .args(&["config", "status.showUntrackedFiles", "no"])
            .current_dir(repo_dir.path())
            .output()?;
        barrier();

        let actual = ModuleRenderer::new("git_status")
            .path(&repo_dir.path())
            .collect();
        let expected = None;

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_stashed() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;
        barrier();

        create_stash(repo_dir.path())?;

        create_command("git")?
            .args(&["reset", "--hard", "HEAD"])
            .current_dir(repo_dir.path())
            .output()?;
        barrier();

        let actual = ModuleRenderer::new("git_status")
            .path(&repo_dir.path())
            .collect();
        let expected = format_output("$");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_stashed_with_count() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;
        barrier();

        create_stash(repo_dir.path())?;
        barrier();

        create_command("git")?
            .args(&["reset", "--hard", "HEAD"])
            .current_dir(repo_dir.path())
            .output()?;
        barrier();

        let actual = ModuleRenderer::new("git_status")
            .config(toml::toml! {
                [git_status]
                stashed = r"\$$count"
            })
            .path(&repo_dir.path())
            .collect();
        let expected = format_output("$1");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_modified() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        create_modified(repo_dir.path())?;

        let actual = ModuleRenderer::new("git_status")
            .path(&repo_dir.path())
            .collect();
        let expected = format_output("!");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_modified_with_count() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        create_modified(repo_dir.path())?;

        let actual = ModuleRenderer::new("git_status")
            .config(toml::toml! {
                [git_status]
                modified = "!$count"
            })
            .path(&repo_dir.path())
            .collect();
        let expected = format_output("!1");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_added() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        create_added(repo_dir.path())?;

        let actual = ModuleRenderer::new("git_status")
            .path(&repo_dir.path())
            .collect();
        let expected = format_output("!");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_staged_file() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        create_staged(repo_dir.path())?;

        let actual = ModuleRenderer::new("git_status")
            .path(&repo_dir.path())
            .collect();
        let expected = format_output("+");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_staged_file_with_count() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        create_staged(repo_dir.path())?;

        let actual = ModuleRenderer::new("git_status")
            .config(toml::toml! {
                [git_status]
                staged = "+[$count](green)"
            })
            .path(&repo_dir.path())
            .collect();
        let expected = Some(format!(
            "{} ",
            ANSIStrings(&[
                Color::Red.bold().paint("[+"),
                Color::Green.paint("1"),
                Color::Red.bold().paint("]"),
            ])
        ));

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_staged_and_modified_file() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        create_staged_and_modified(repo_dir.path())?;

        let actual = ModuleRenderer::new("git_status")
            .path(&repo_dir.path())
            .collect();
        let expected = format_output("!+");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_renamed_file() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        create_renamed(repo_dir.path())?;

        let actual = ModuleRenderer::new("git_status")
            .path(&repo_dir.path())
            .collect();
        let expected = format_output("»");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_renamed_file_with_count() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        create_renamed(repo_dir.path())?;

        let actual = ModuleRenderer::new("git_status")
            .config(toml::toml! {
                [git_status]
                renamed = "»$count"
            })
            .path(&repo_dir.path())
            .collect();
        let expected = format_output("»1");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_renamed_and_modified_file() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        create_renamed_and_modified(repo_dir.path())?;

        let actual = ModuleRenderer::new("git_status")
            .path(&repo_dir.path())
            .collect();
        let expected = format_output("»!");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_deleted_file() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        create_deleted(repo_dir.path())?;

        let actual = ModuleRenderer::new("git_status")
            .path(&repo_dir.path())
            .collect();
        let expected = format_output("✘");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn shows_deleted_file_with_count() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        create_deleted(repo_dir.path())?;

        let actual = ModuleRenderer::new("git_status")
            .config(toml::toml! {
                [git_status]
                deleted = "✘$count"
            })
            .path(&repo_dir.path())
            .collect();
        let expected = format_output("✘1");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn doesnt_show_ignored_file() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        create_staged_and_ignored(repo_dir.path())?;

        let actual = ModuleRenderer::new("git_status")
            .path(&repo_dir.path())
            .collect();
        let expected = format_output("+");

        assert_eq!(expected, actual);
        repo_dir.close()
    }

    #[test]
    fn worktree_in_different_dir() -> io::Result<()> {
        let worktree_dir = tempfile::tempdir()?;
        let repo_dir = fixture_repo(FixtureProvider::Git)?;

        create_command("git")?
            .args(&[
                OsStr::new("config"),
                OsStr::new("core.worktree"),
                worktree_dir.path().as_os_str(),
            ])
            .current_dir(repo_dir.path())
            .output()?;

        File::create(worktree_dir.path().join("test_file"))?.sync_all()?;

        let actual = ModuleRenderer::new("git_status")
            .path(&repo_dir.path())
            .collect();
        let expected = format_output("✘?");

        assert_eq!(expected, actual);
        worktree_dir.close()?;
        repo_dir.close()
    }

    // Whenever a file is manually renamed, git itself ('git status') does not treat such file as renamed,
    // but as untracked instead. The following test checks if manually deleted and manually renamed
    // files are tracked by git_status module in the same way 'git status' does.
    #[test]
    #[ignore]
    fn ignore_manually_renamed() -> io::Result<()> {
        let repo_dir = fixture_repo(FixtureProvider::Git)?;
        File::create(repo_dir.path().join("a"))?.sync_all()?;
        File::create(repo_dir.path().join("b"))?.sync_all()?;
        create_command("git")?
            .args(&["add", "--all"])
            .current_dir(&repo_dir.path())
            .output()?;
        create_command("git")?
            .args(&["commit", "-m", "add new files", "--no-gpg-sign"])
            .current_dir(&repo_dir.path())
            .output()?;

        fs::remove_file(repo_dir.path().join("a"))?;
        fs::rename(repo_dir.path().join("b"), repo_dir.path().join("c"))?;
        barrier();

        let actual = ModuleRenderer::new("git_status")
            .path(&repo_dir.path())
            .config(toml::toml! {
                [git_status]
                ahead = "A"
                deleted = "D"
                untracked = "U"
                renamed = "R"
            })
            .collect();
        let expected = format_output("DUA");

        assert_eq!(actual, expected);

        repo_dir.close()
    }

    fn ahead(repo_dir: &Path) -> io::Result<()> {
        File::create(repo_dir.join("readme.md"))?.sync_all()?;

        create_command("git")?
            .args(&["commit", "-am", "Update readme", "--no-gpg-sign"])
            .current_dir(&repo_dir)
            .output()?;
        barrier();

        Ok(())
    }

    fn behind(repo_dir: &Path) -> io::Result<()> {
        create_command("git")?
            .args(&["reset", "--hard", "HEAD^"])
            .current_dir(repo_dir)
            .output()?;
        barrier();

        Ok(())
    }

    fn diverge(repo_dir: &Path) -> io::Result<()> {
        create_command("git")?
            .args(&["reset", "--hard", "HEAD^"])
            .current_dir(repo_dir)
            .output()?;
        barrier();

        fs::write(repo_dir.join("Cargo.toml"), " ")?;

        create_command("git")?
            .args(&["commit", "-am", "Update readme", "--no-gpg-sign"])
            .current_dir(repo_dir)
            .output()?;
        barrier();

        Ok(())
    }

    fn create_conflict(repo_dir: &Path) -> io::Result<()> {
        create_command("git")?
            .args(&["reset", "--hard", "HEAD^"])
            .current_dir(repo_dir)
            .output()?;
        barrier();

        fs::write(repo_dir.join("readme.md"), "# goodbye")?;

        create_command("git")?
            .args(&["add", "."])
            .current_dir(repo_dir)
            .output()?;
        barrier();

        create_command("git")?
            .args(&["commit", "-m", "Change readme", "--no-gpg-sign"])
            .current_dir(repo_dir)
            .output()?;
        barrier();

        create_command("git")?
            .args(&["pull", "--rebase"])
            .current_dir(repo_dir)
            .output()?;
        barrier();

        Ok(())
    }

    fn create_stash(repo_dir: &Path) -> io::Result<()> {
        File::create(repo_dir.join("readme.md"))?.sync_all()?;
        barrier();

        create_command("git")?
            .args(&["stash", "--all"])
            .current_dir(repo_dir)
            .output()?;
        barrier();

        Ok(())
    }

    fn create_untracked(repo_dir: &Path) -> io::Result<()> {
        File::create(repo_dir.join("license"))?.sync_all()?;

        Ok(())
    }

    fn create_added(repo_dir: &Path) -> io::Result<()> {
        File::create(repo_dir.join("license"))?.sync_all()?;

        create_command("git")?
            .args(&["add", "-A", "-N"])
            .current_dir(repo_dir)
            .output()?;
        barrier();

        Ok(())
    }

    fn create_modified(repo_dir: &Path) -> io::Result<()> {
        File::create(repo_dir.join("readme.md"))?.sync_all()?;

        Ok(())
    }

    fn create_staged(repo_dir: &Path) -> io::Result<()> {
        File::create(repo_dir.join("license"))?.sync_all()?;

        create_command("git")?
            .args(&["add", "."])
            .current_dir(repo_dir)
            .output()?;
        barrier();

        Ok(())
    }

    fn create_staged_and_modified(repo_dir: &Path) -> io::Result<()> {
        let mut file = File::create(repo_dir.join("readme.md"))?;
        file.sync_all()?;

        create_command("git")?
            .args(&["add", "."])
            .current_dir(repo_dir)
            .output()?;
        barrier();

        writeln!(&mut file, "modified")?;
        file.sync_all()?;

        Ok(())
    }

    fn create_renamed(repo_dir: &Path) -> io::Result<()> {
        create_command("git")?
            .args(&["mv", "readme.md", "readme.md.bak"])
            .current_dir(repo_dir)
            .output()?;
        barrier();

        create_command("git")?
            .args(&["add", "-A"])
            .current_dir(repo_dir)
            .output()?;
        barrier();

        Ok(())
    }

    fn create_renamed_and_modified(repo_dir: &Path) -> io::Result<()> {
        create_command("git")?
            .args(&["mv", "readme.md", "readme.md.bak"])
            .current_dir(repo_dir)
            .output()?;
        barrier();

        create_command("git")?
            .args(&["add", "-A"])
            .current_dir(repo_dir)
            .output()?;
        barrier();

        let mut file = File::create(repo_dir.join("readme.md.bak"))?;
        writeln!(&mut file, "modified")?;
        file.sync_all()?;

        Ok(())
    }

    fn create_deleted(repo_dir: &Path) -> io::Result<()> {
        fs::remove_file(repo_dir.join("readme.md"))?;

        Ok(())
    }

    fn create_staged_and_ignored(repo_dir: &Path) -> io::Result<()> {
        let mut file = File::create(repo_dir.join(".gitignore"))?;
        writeln!(&mut file, "ignored.txt")?;
        file.sync_all()?;

        create_command("git")?
            .args(&["add", ".gitignore"])
            .current_dir(repo_dir)
            .output()?;
        barrier();

        let mut file = File::create(repo_dir.join("ignored.txt"))?;
        writeln!(&mut file, "modified")?;
        file.sync_all()?;

        Ok(())
    }
}
