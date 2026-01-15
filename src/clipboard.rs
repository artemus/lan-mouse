use sha2::{Digest, Sha256};
use std::fmt;

#[derive(Debug)]
pub enum ClipboardError {
    #[cfg(target_os = "linux")]
    Io(std::io::Error),
    #[cfg(not(target_os = "linux"))]
    Arboard(arboard::Error),
}

impl fmt::Display for ClipboardError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            #[cfg(target_os = "linux")]
            ClipboardError::Io(err) => write!(f, "{err}"),
            #[cfg(not(target_os = "linux"))]
            ClipboardError::Arboard(err) => write!(f, "{err}"),
        }
    }
}

pub struct ClipboardSync {
    #[cfg(target_os = "linux")]
    backend: LinuxClipboard,
    #[cfg(not(target_os = "linux"))]
    backend: arboard::Clipboard,
    last_hash: Option<String>,
}

impl ClipboardSync {
    pub fn new() -> Result<Self, ClipboardError> {
        #[cfg(target_os = "linux")]
        let backend = LinuxClipboard::new().map_err(ClipboardError::Io)?;
        #[cfg(not(target_os = "linux"))]
        let backend = arboard::Clipboard::new().map_err(ClipboardError::Arboard)?;
        Ok(Self {
            backend,
            last_hash: None,
        })
    }

    pub fn poll(&mut self) -> Result<Option<String>, ClipboardError> {
        let text = self.get_text()?;
        if text.is_empty() {
            return Ok(None);
        }
        let hash = hash_text(&text);
        if self.last_hash.as_deref() == Some(&hash) {
            return Ok(None);
        }
        self.last_hash = Some(hash);
        Ok(Some(text))
    }

    pub fn set_text(&mut self, text: &str) -> Result<(), ClipboardError> {
        self.set_text_inner(text)?;
        self.last_hash = Some(hash_text(text));
        Ok(())
    }

    fn get_text(&mut self) -> Result<String, ClipboardError> {
        #[cfg(target_os = "linux")]
        {
            self.backend.get_text().map_err(ClipboardError::Io)
        }
        #[cfg(not(target_os = "linux"))]
        {
            self.backend
                .get_text()
                .map_err(ClipboardError::Arboard)
        }
    }

    fn set_text_inner(&mut self, text: &str) -> Result<(), ClipboardError> {
        #[cfg(target_os = "linux")]
        {
            self.backend.set_text(text).map_err(ClipboardError::Io)
        }
        #[cfg(not(target_os = "linux"))]
        {
            self.backend
                .set_text(text.to_owned())
                .map_err(ClipboardError::Arboard)
        }
    }
}

#[cfg(target_os = "linux")]
struct LinuxClipboard;

#[cfg(target_os = "linux")]
impl LinuxClipboard {
    fn new() -> Result<Self, std::io::Error> {
        Ok(Self)
    }

    fn get_text(&self) -> Result<String, std::io::Error> {
        let attempts = [
            ["-n", "--type", "text/plain;charset=utf-8"].as_slice(),
            ["-n", "--type", "text/plain"].as_slice(),
            ["-n"].as_slice(),
        ];
        for args in attempts {
            let output = std::process::Command::new("wl-paste").args(args).output()?;
            if !output.status.success() {
                continue;
            }
            let text = String::from_utf8_lossy(&output.stdout).to_string();
            if !text.is_empty() {
                return Ok(text);
            }
        }
        Ok(String::new())
    }

    fn set_text(&self, text: &str) -> Result<(), std::io::Error> {
        let mut child = std::process::Command::new("wl-copy")
            .args(["--type", "text/plain;charset=utf-8"])
            .stdin(std::process::Stdio::piped())
            .spawn()?;
        if let Some(stdin) = child.stdin.as_mut() {
            use std::io::Write;
            stdin.write_all(text.as_bytes())?;
        }
        let status = child.wait()?;
        if !status.success() {
            return Err(std::io::Error::new(
                std::io::ErrorKind::Other,
                "wl-copy failed",
            ));
        }
        Ok(())
    }
}

fn hash_text(text: &str) -> String {
    let mut hash = Sha256::new();
    hash.update(text.as_bytes());
    let bytes = hash
        .finalize()
        .iter()
        .map(|x| format!("{x:02x}"))
        .collect::<Vec<_>>();
    bytes.join(":")
}
