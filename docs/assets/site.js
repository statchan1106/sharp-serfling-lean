const toast = document.querySelector("#toast");

document.querySelectorAll("[data-project-link]").forEach((placeholder) => {
  const key = placeholder.dataset.projectLink;
  const url = window.SHARP_SERFLING_LINKS?.[key];
  if (!url) {
    placeholder.remove();
    return;
  }

  const link = document.createElement("a");
  link.href = url;
  link.textContent = placeholder.dataset.liveLabel ?? placeholder.textContent;
  link.rel = "noopener noreferrer";
  placeholder.replaceWith(link);
});

function showToast(message = "Copied") {
  if (!toast) return;
  toast.textContent = message;
  toast.classList.add("show");
  window.clearTimeout(showToast.timeout);
  showToast.timeout = window.setTimeout(() => toast.classList.remove("show"), 1400);
}

async function copyText(text) {
  try {
    await navigator.clipboard.writeText(text);
    showToast();
  } catch (_) {
    showToast("Copy unavailable");
  }
}

document.querySelectorAll("[data-copy]").forEach((button) => {
  button.addEventListener("click", () => copyText(button.dataset.copy));
});

document.querySelector("#copy-commands")?.addEventListener("click", () => {
  copyText(document.querySelector("#verification-commands")?.textContent ?? "");
});

const filter = document.querySelector("#declaration-filter");
const cards = [...document.querySelectorAll(".declaration-card")];
const count = document.querySelector("#result-count");
const noResults = document.querySelector("#no-results");

filter?.addEventListener("input", () => {
  const query = filter.value.trim().toLowerCase();
  let visible = 0;
  cards.forEach((card) => {
    const haystack = `${card.dataset.group ?? ""} ${card.textContent}`.toLowerCase();
    const matches = haystack.includes(query);
    card.hidden = !matches;
    visible += Number(matches);
  });
  if (count) count.textContent = `${visible} result group${visible === 1 ? "" : "s"}`;
  if (noResults) noResults.hidden = visible !== 0;
});
