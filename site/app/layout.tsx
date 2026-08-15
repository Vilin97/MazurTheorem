import type { Metadata, Viewport } from "next";
import { headers } from "next/headers";
import programData from "../generated/program.json";
import "./globals.css";

const FALLBACK_SITE_ORIGIN =
  "https://mazur-theorem-formalization.vilin402100.chatgpt.site/";
const DESCRIPTION =
  "An open, weighted roadmap for the full fifteen-group classification in Mazur’s rational torsion theorem.";
const SOCIAL_DESCRIPTION =
  "Canonical modular curves, Jacobians, Néron models, exact Lean contracts, and evidence-weighted progress.";
const INTEGRATED_PERCENT = Math.max(
  0,
  Math.min(100, programData.progress.percent),
);

function normalizedOrigin(origin: string) {
  return origin.endsWith("/") ? origin : `${origin}/`;
}

function parseOrigin(origin: string) {
  try {
    const parsed = new URL(origin);
    if (parsed.protocol !== "http:" && parsed.protocol !== "https:") {
      return undefined;
    }
    return normalizedOrigin(parsed.origin);
  } catch {
    return undefined;
  }
}

async function requestedOrigin() {
  const configuredOrigin = process.env.NEXT_PUBLIC_SITE_URL;
  if (configuredOrigin) {
    return parseOrigin(configuredOrigin) ?? FALLBACK_SITE_ORIGIN;
  }

  const requestHeaders = await headers();
  const forwardedHost = requestHeaders
    .get("x-forwarded-host")
    ?.split(",", 1)[0]
    ?.trim();
  const host = forwardedHost ?? requestHeaders.get("host");
  if (!host) {
    return FALLBACK_SITE_ORIGIN;
  }

  const forwardedProtocol = requestHeaders
    .get("x-forwarded-proto")
    ?.split(",", 1)[0]
    ?.trim();
  const protocol =
    forwardedProtocol === "http" || forwardedProtocol === "https"
      ? forwardedProtocol
      : host.startsWith("localhost")
        ? "http"
        : "https";
  return parseOrigin(`${protocol}://${host}`) ?? FALLBACK_SITE_ORIGIN;
}

export async function generateMetadata(): Promise<Metadata> {
  const origin = await requestedOrigin();
  const image = new URL("og-v2.png", origin).toString();

  return {
    metadataBase: new URL(origin),
    alternates: { canonical: origin },
    title: {
      default: "Mazur Theorem · Formalization Programme",
      template: "%s · Mazur Theorem",
    },
    description: DESCRIPTION,
    keywords: [
      "Mazur theorem",
      "Lean 4",
      "formal mathematics",
      "elliptic curves",
      "crowdsourcing",
    ],
    authors: [{ name: "Mazur Theorem contributors" }],
    openGraph: {
      title: "Mazur Theorem · Formalization Programme",
      description: SOCIAL_DESCRIPTION,
      type: "website",
      siteName: "Mazur Theorem",
      images: [
        {
          url: image,
          width: 1200,
          height: 630,
          alt: `Mazur Theorem formalization programme — ${INTEGRATED_PERCENT}% integrated`,
        },
      ],
    },
    twitter: {
      card: "summary_large_image",
      title: "Mazur Theorem · Formalization Programme",
      description: SOCIAL_DESCRIPTION,
      images: [image],
    },
    robots: {
      index: true,
      follow: true,
    },
  };
}

export const viewport: Viewport = {
  colorScheme: "light",
  themeColor: "#f2ecdf",
};

export default function RootLayout({
  children,
}: Readonly<{
  children: React.ReactNode;
}>) {
  return (
    <html lang="en">
      <body>{children}</body>
    </html>
  );
}
