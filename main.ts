// Entry point for the forge: start the app, register with the trial suite,
// and exit once the suite says it is done.
//
// Lifecycle (see the kit's RULES.txt, "The suite and the wire"):
//   1. Bind an ephemeral port (port 0 lets the kernel pick one).
//   2. POST {"port": <the port>} to $MAKEFUN_ENV_URL/register.
//   3. Long-poll GET $MAKEFUN_ENV_URL/done until it answers {"done": true},
//      then exit 0. A program that never registers scores 0, so registering
//      is retried until it succeeds.
// Without MAKEFUN_ENV_URL there is no suite to report to, so the forge just
// stays up serving on its ephemeral port.
import { createApp } from "./app.ts";

const POLL_MS = 500;

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

// POST the listening port to the suite, retrying until the suite accepts it.
async function register(envUrl: string, port: number): Promise<void> {
  for (;;) {
    try {
      const res = await fetch(`${envUrl}/register`, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({ port }),
      });
      if (res.ok) return;
    } catch {
      // The suite may not be listening yet; try again.
    }
    await sleep(POLL_MS);
  }
}

// Poll the suite until it reports the trial is finished.
async function waitForDone(envUrl: string): Promise<void> {
  for (;;) {
    try {
      const res = await fetch(`${envUrl}/done`);
      if (res.ok) {
        const body: unknown = await res.json();
        if (
          typeof body === "object" &&
          body !== null &&
          (body as { done?: unknown }).done === true
        ) {
          return;
        }
      }
    } catch {
      // A transient failure is not a reason to stop polling.
    }
    await sleep(POLL_MS);
  }
}

async function main(): Promise<void> {
  const envUrl = process.env.MAKEFUN_ENV_URL;
  const server = createApp();

  const port = await new Promise<number>((resolve, reject) => {
    server.once("error", reject);
    server.listen(0, "0.0.0.0", () => {
      const addr = server.address();
      if (addr !== null && typeof addr === "object") resolve(addr.port);
      else reject(new Error("could not determine listening port"));
    });
  });

  if (!envUrl) return; // Standalone: keep serving on the ephemeral port.
  await register(envUrl, port);
  await waitForDone(envUrl);
  server.close();
  process.exit(0);
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
