//! Lemma edit / delete / add form bodies (the `html` field of the `main/edit`,
//! `main/delete`, `main/add` JSON envelopes).
//!
//! These are near-static templates. The variable slots are the lemma name (and,
//! for edit, the current lemma text). The form `action` attribute is a relative
//! URL `../../edit/{verb}/{name}` where `{name}` is HTML-escaped (so the add
//! placeholder `<first>` renders as `&lt;first&gt;`). The edit textarea content
//! is the raw lemma source, HTML-escaped.
//!
//! Use [`super::envelope::render_content`] to wrap these in the JSON envelope
//! with the appropriate title.

use super::escape::html_escape;

/// Body of the edit-lemma form for lemma `name` whose current text is `text`.
/// Title used by the caller: `"Edit Lemma: {name}"`.
pub fn edit_form(name: &str, text: &str) -> String {
    let action = html_escape(name);
    let body = html_escape(text);
    format!(
        r#"<form method="post" action="../../edit/edit/{action}"><div contenteditable="true"><label for="lemmaTextArea"> Edit Lemma {name}</label>
<textarea name="lemma-text" id="lemmaTextArea" rows="8">{body}</textarea>
</div>
<button type="submit">Submit</button>
<p></p>
<h3> Introduction to Lemma Edit:</h3>
<noscript><div class="warning">Warning: JavaScript must be enabled for the
<span class="tamarin">Tamarin</span></span>
prover GUI to function properly.</div>
</noscript>
<p><ul class="wrap-text"><li>Modifying the lemma in the box above and clicking the submit button will attempt to modify the lemma in the current theory.
<br>&zwnj;</br>
</li>
<li>Failures in parsing the lemma or verifying its well-formedness will result in an error, and the lemma will NOT be modified.
However, your changes will be kept on this page until you leave this right panel.
<br>&zwnj;</br>
</li>
<li>Editing a lemma will NOT modify the file it was loaded from, but clicking on "Append modified lemmas to file" in the Actions menu adds all modified lemmas as a comment at the end of the file on disk they were loaded from.
<br>&zwnj;</br>
</li>
<li>Clicking on "Download source" in the Actions menu will download the modified version of the theory (including the modified lemmas), but not modify the file on disk.
<br>&zwnj;</br>
</li>
<li>Modifying a reuse lemma will invalidate all subsequent proofs.
<br>&zwnj;</br>
</li>
<li>Modifying a sources lemma is not supported and will result in an error.</li>
</ul>
<style>.wrap-text li {{white-space: normal;
word-wrap: break-word;}}</style>
</p>
</form>
"#
    )
}

/// Body of the delete-lemma confirmation for lemma `name`.
/// Title used by the caller: `"Delete {name}"`.
pub fn delete_form(name: &str) -> String {
    let action = html_escape(name);
    format!(
        r#"<p> Do you want to delete lemma {name}?</p>
<form method="post" action="../../edit/delete/{action}"><button type="submit">Yes</button>
<p></p>
<h3> Introduction to Lemma Delete:</h3>
<noscript><div class="warning">Warning: JavaScript must be enabled for the
<span class="tamarin">Tamarin</span></span>
prover GUI to function properly.</div>
</noscript>
<p><ul class="wrap-text"><li>Clicking on the button above will delete the lemma from the loaded theory.
<br>&zwnj;</br>
</li>
<li>Deleting a lemma will NOT modify the file it was loaded from, but clicking on "Download source" in the Actions menu will download the modified version of the theory (so without the deleted lemmas).
<br>&zwnj;</br>
</li>
<li>Deleting a reuse lemma will invalidate all subsequent proofs.
<br>&zwnj;</br>
</li>
<li>Deleting a source lemma is not supported and will result in an error.</li>
<style>.wrap-text li {{white-space: normal;
word-wrap: break-word;}}</style>
</ul>
</p>
</form>
"#
    )
}

/// Body of the add-lemma form. `target` is the position marker: a lemma name,
/// or `"<first>"` for the top position. Title used by the caller:
/// `"Add new Lemma"`.
pub fn add_form(target: &str) -> String {
    let action = html_escape(target);
    format!(
        r#"<form method="post" action="../../edit/add/{action}"><div contenteditable="true"><label for="lemmaTextArea">LemmaText</label>
<textarea name="lemma-text" id="lemmaTextArea">Enter your new Lemma</textarea>
</div>
<button type="submit">Submit</button>
<p></p>
<h3> Introduction to Adding Lemmas:</h3>
<noscript><div class="warning">Warning: JavaScript must be enabled for the
<span class="tamarin">Tamarin</span></span>
prover GUI to function properly.</div>
</noscript>
<p><ul class="wrap-text"><li>Adds the lemma in the current position in the theory, but will throw an error if a lemma with the same name exists, the parsing fails, or the lemma isn't well-formed.
<br>&zwnj;</br>
</li>
<li>Adding a lemma will NOT modify the loaded source file, but clicking on "Append modified lemmas to file" in the Actions menu appends all added lemmas as a comment at the end of the current theory file.
<br>&zwnj;</br>
</li>
<li>Clicking on "Download source" in the Actions menu will download the modified version of the theory (including the added lemmas).</li>
</ul>
<style>.wrap-text li {{white-space: normal;
word-wrap: break-word;}}</style>
</p>
</form>
"#
    )
}
