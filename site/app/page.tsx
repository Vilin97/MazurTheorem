import programData from "../generated/program.json";
import { ProgrammeDashboard } from "./programme-dashboard";
import type { Programme } from "./programme-types";

export default function Home() {
  return <ProgrammeDashboard programme={programData as Programme} />;
}
