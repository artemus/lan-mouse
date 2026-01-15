use arboard::Clipboard;
use sha2::{Digest, Sha256};

pub struct ClipboardSync {
    clipboard: Clipboard,
    last_hash: Option<String>,
}

impl ClipboardSync {
    pub fn new() -> Result<Self, arboard::Error> {
        Ok(Self {
            clipboard: Clipboard::new()?,
            last_hash: None,
        })
    }

    pub fn poll(&mut self) -> Result<Option<String>, arboard::Error> {
        let text = self.clipboard.get_text()?;
        let hash = hash_text(&text);
        if self.last_hash.as_deref() == Some(&hash) {
            return Ok(None);
        }
        self.last_hash = Some(hash);
        Ok(Some(text))
    }

    pub fn set_text(&mut self, text: &str) -> Result<(), arboard::Error> {
        self.clipboard.set_text(text.to_owned())?;
        self.last_hash = Some(hash_text(text));
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
