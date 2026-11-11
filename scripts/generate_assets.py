#!/usr/bin/env python3
"""
Procedurally generates bespoke 3D mathematical sculptures (.usdz for Apple Vision Pro
native <model stagemode="orbit"> + iOS AR Quick Look, and .glb for WebGL <model-viewer>)
and dark/light-adaptive SVG mathematical diagrams for the Verso edition of
Goldblatt's *Lectures on the Hyperreals*.
"""

from __future__ import annotations

import math
import shutil
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

import numpy as np
import trimesh

ROOT = Path(__file__).resolve().parent.parent
STATIC_DIR = ROOT / "static"
MODELS_DIR = STATIC_DIR / "models"
DIAGRAMS_DIR = STATIC_DIR / "diagrams"


@dataclass
class PBRMat:
    name: str
    diffuse: tuple[float, float, float]
    metallic: float = 0.15
    roughness: float = 0.32
    opacity: float = 1.0
    emissive: tuple[float, float, float] = (0.0, 0.0, 0.0)


@dataclass
class SceneBuilder:
    name: str
    buckets: dict[str, tuple[PBRMat, list[trimesh.Trimesh]]] = field(default_factory=dict)

    def add(self, mat: PBRMat, mesh: trimesh.Trimesh) -> None:
        if mat.name not in self.buckets:
            self.buckets[mat.name] = (mat, [])
        m = mesh.copy()
        m.process(validate=True)
        self.buckets[mat.name][1].append(m)

    def add_sphere(self, mat: PBRMat, center: Iterable[float], radius: float, subdivisions: int = 3) -> None:
        m = trimesh.creation.icosphere(subdivisions=subdivisions, radius=radius)
        m.apply_translation(np.asarray(center, dtype=float))
        self.add(mat, m)

    def add_box(self, mat: PBRMat, extents: Iterable[float], center: Iterable[float] = (0, 0, 0)) -> None:
        m = trimesh.creation.box(extents=np.asarray(extents, dtype=float))
        m.apply_translation(np.asarray(center, dtype=float))
        self.add(mat, m)

    def add_torus(
        self,
        mat: PBRMat,
        major_radius: float,
        minor_radius: float,
        center: Iterable[float] = (0, 0, 0),
        axis: str = "y",
        major_sections: int = 48,
        minor_sections: int = 20,
    ) -> None:
        m = trimesh.creation.torus(
            major_radius=major_radius,
            minor_radius=minor_radius,
            major_sections=major_sections,
            minor_sections=minor_sections,
        )
        # trimesh torus lies in XY plane (normal along Z)
        if axis == "y":
            rot = trimesh.transformations.rotation_matrix(math.pi / 2.0, [1, 0, 0])
            m.apply_transform(rot)
        elif axis == "x":
            rot = trimesh.transformations.rotation_matrix(math.pi / 2.0, [0, 1, 0])
            m.apply_transform(rot)
        m.apply_translation(np.asarray(center, dtype=float))
        self.add(mat, m)

    def add_segment(
        self,
        mat: PBRMat,
        p0: Iterable[float],
        p1: Iterable[float],
        radius: float,
        sections: int = 16,
    ) -> None:
        a = np.asarray(p0, dtype=float)
        b = np.asarray(p1, dtype=float)
        if np.linalg.norm(b - a) < 1e-6:
            return
        m = trimesh.creation.cylinder(radius=radius, segment=np.vstack([a, b]), sections=sections)
        self.add(mat, m)

    def add_cone_between(
        self,
        mat: PBRMat,
        base: Iterable[float],
        tip: Iterable[float],
        radius: float,
        sections: int = 20,
    ) -> None:
        a = np.asarray(base, dtype=float)
        b = np.asarray(tip, dtype=float)
        vec = b - a
        height = float(np.linalg.norm(vec))
        if height < 1e-6:
            return
        m = trimesh.creation.cone(radius=radius, height=height, sections=sections)
        # trimesh cone base is at z=0, tip at z=height
        z_axis = np.array([0.0, 0.0, 1.0])
        direction = vec / height
        align = trimesh.geometry.align_vectors(z_axis, direction)
        m.apply_transform(align)
        m.apply_translation(a)
        self.add(mat, m)

    def add_polyline_tube(
        self,
        mat: PBRMat,
        points: np.ndarray,
        radius: float,
        sections: int = 12,
        sphere_joints: bool = False,
    ) -> None:
        for i in range(len(points) - 1):
            self.add_segment(mat, points[i], points[i + 1], radius=radius, sections=sections)
            if sphere_joints and i > 0:
                self.add_sphere(mat, points[i], radius=radius * 1.02, subdivisions=1)

    def write_usda(self, usda_path: Path) -> None:
        lines: list[str] = [
            "#usda 1.0",
            "(",
            '    defaultPrim = "Scene"',
            "    metersPerUnit = 1",
            '    upAxis = "Y"',
            ")",
            "",
            'def Xform "Scene"',
            "{",
            '    def Scope "Materials"',
            "    {",
        ]
        # Emit PBR materials first
        for mat_name, (mat, _) in self.buckets.items():
            r, g, b = mat.diffuse
            er, eg, eb = mat.emissive
            lines.extend(
                [
                    f'        def Material "{mat_name}"',
                    "        {",
                    f'            token outputs:surface.connect = </Scene/Materials/{mat_name}/PBRShader.outputs:surface>',
                    '            def Shader "PBRShader"',
                    "            {",
                    '                uniform token info:id = "UsdPreviewSurface"',
                    f"                color3f inputs:diffuseColor = ({r:.4f}, {g:.4f}, {b:.4f})",
                    f"                color3f inputs:emissiveColor = ({er:.4f}, {eg:.4f}, {eb:.4f})",
                    f"                float inputs:metallic = {mat.metallic:.4f}",
                    f"                float inputs:roughness = {mat.roughness:.4f}",
                    f"                float inputs:opacity = {mat.opacity:.4f}",
                    "                token outputs:surface",
                    "            }",
                    "        }",
                ]
            )
        lines.append("    }")
        lines.append('    def Xform "Geometry"')
        lines.append("    {")

        for mat_name, (mat, meshes) in self.buckets.items():
            combined = trimesh.util.concatenate(meshes)
            combined.remove_unreferenced_vertices()
            verts = np.asarray(combined.vertices, dtype=float)
            faces = np.asarray(combined.faces, dtype=int)
            vnormals = np.asarray(combined.vertex_normals, dtype=float)

            vmin = verts.min(axis=0)
            vmax = verts.max(axis=0)
            counts_str = ", ".join(["3"] * len(faces))
            indices_str = ", ".join(str(int(idx)) for idx in faces.reshape(-1))
            pts_str = ", ".join(f"({v[0]:.5f}, {v[1]:.5f}, {v[2]:.5f})" for v in verts)
            nrm_str = ", ".join(f"({n[0]:.4f}, {n[1]:.4f}, {n[2]:.4f})" for n in vnormals)
            double_sided = "true" if mat.opacity < 0.99 else "false"

            lines.extend(
                [
                    f'        def Mesh "Mesh_{mat_name}" (',
                    '            prepend apiSchemas = ["MaterialBindingAPI"]',
                    "        )",
                    "        {",
                    f"            uniform bool doubleSided = {double_sided}",
                    f"            float3[] extent = [({vmin[0]:.5f}, {vmin[1]:.5f}, {vmin[2]:.5f}), ({vmax[0]:.5f}, {vmax[1]:.5f}, {vmax[2]:.5f})]",
                    f"            int[] faceVertexCounts = [{counts_str}]",
                    f"            int[] faceVertexIndices = [{indices_str}]",
                    f"            rel material:binding = </Scene/Materials/{mat_name}>",
                    f"            normal3f[] normals = [{nrm_str}] (",
                    '                interpolation = "vertex"',
                    "            )",
                    f"            point3f[] points = [{pts_str}]",
                    '            uniform token subdivisionScheme = "none"',
                    "        }",
                ]
            )

        lines.append("    }")
        lines.append("}")
        usda_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    def export_glb_and_usdz(self, out_dir: Path) -> tuple[Path, Path]:
        out_dir.mkdir(parents=True, exist_ok=True)
        glb_path = out_dir / f"{self.name}.glb"
        usdz_path = out_dir / f"{self.name}.usdz"

        # 1. Export GLB with PBRMaterial per bucket
        scene = trimesh.Scene()
        # Draw opaque buckets first, translucent buckets last
        ordered = sorted(self.buckets.values(), key=lambda pair: (pair[0].opacity < 0.99))
        for mat, meshes in ordered:
            combined = trimesh.util.concatenate(meshes)
            combined.remove_unreferenced_vertices()
            base_rgba = [
                int(round(mat.diffuse[0] * 255)),
                int(round(mat.diffuse[1] * 255)),
                int(round(mat.diffuse[2] * 255)),
                int(round(mat.opacity * 255)),
            ]
            pbr = trimesh.visual.material.PBRMaterial(
                name=mat.name,
                baseColorFactor=base_rgba,
                metallicFactor=mat.metallic,
                roughnessFactor=mat.roughness,
                emissiveFactor=list(mat.emissive),
                alphaMode="BLEND" if mat.opacity < 0.99 else "OPAQUE",
                doubleSided=(mat.opacity < 0.99),
            )
            combined.visual = trimesh.visual.TextureVisuals(material=pbr)
            scene.add_geometry(combined, node_name=f"Mesh_{mat.name}")
        glb_bytes = scene.export(file_type="glb")
        glb_path.write_bytes(glb_bytes)

        # 2. Export USDA -> binary USDC -> RealityKit-validated USDZ
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            usda_file = tmp_dir / f"{self.name}.usda"
            usdc_file = tmp_dir / f"{self.name}.usdc"
            self.write_usda(usda_file)
            subprocess.run(["/usr/bin/usdcat", str(usda_file), "-o", str(usdc_file)], check=True)
            if usdz_path.exists():
                usdz_path.unlink()
            subprocess.run(
                ["/usr/bin/usdzip", "--arkitAsset", str(usdc_file), "-c", str(usdz_path)],
                check=True,
            )
            subprocess.run(
                ["/usr/bin/usdchecker", "--arkit", "--strict", str(usdz_path)],
                check=True,
            )

        return usdz_path, glb_path


# Shared signature materials tuned for spatial glass & studio lighting
MAT_SLATE = PBRMat("ObsidianSlate", (0.13, 0.16, 0.24), metallic=0.45, roughness=0.35)
MAT_SILVER = PBRMat("StandardSilver", (0.82, 0.87, 0.95), metallic=0.65, roughness=0.22)
MAT_GOLD = PBRMat("HyperGold", (0.96, 0.74, 0.24), metallic=0.72, roughness=0.20, emissive=(0.08, 0.05, 0.01))
MAT_CYAN = PBRMat("InfinitesimalCyan", (0.14, 0.78, 0.92), metallic=0.25, roughness=0.22, emissive=(0.02, 0.10, 0.14))
MAT_VIOLET = PBRMat("UltrafilterViolet", (0.56, 0.34, 0.94), metallic=0.30, roughness=0.26, emissive=(0.05, 0.02, 0.10))
MAT_CORAL = PBRMat("UnlimitedCoral", (0.95, 0.38, 0.36), metallic=0.28, roughness=0.28, emissive=(0.08, 0.02, 0.02))
MAT_EMERALD = PBRMat("GalaxyEmerald", (0.16, 0.80, 0.56), metallic=0.28, roughness=0.26, emissive=(0.01, 0.07, 0.04))
MAT_HALO_GLASS = PBRMat("HaloGlass", (0.28, 0.72, 0.98), metallic=0.05, roughness=0.08, opacity=0.34, emissive=(0.02, 0.05, 0.09))
MAT_GOLD_GLASS = PBRMat("ShadowShell", (0.98, 0.80, 0.32), metallic=0.08, roughness=0.12, opacity=0.32, emissive=(0.05, 0.03, 0.01))


def build_hyperreal_telescope() -> SceneBuilder:
    """Model 1: Standard real line R, translucent halo spheres hal(0), hal(1),
    nested infinitesimal rings eps & eps^2, shadow projection beams, and
    floating infinite galaxies gal(+omega) and gal(-omega)."""
    sb = SceneBuilder("hyperreal_telescope")

    # Subtle pedestal ring representing the finite galaxy L
    sb.add_torus(MAT_SLATE, major_radius=0.34, minor_radius=0.006, center=(0, -0.10, 0), axis="y")

    # Standard real line R along X from -0.34 to +0.34
    sb.add_segment(MAT_SILVER, (-0.34, 0.0, 0.0), (0.34, 0.0, 0.0), radius=0.008)
    sb.add_cone_between(MAT_SILVER, (0.34, 0.0, 0.0), (0.38, 0.0, 0.0), radius=0.018)
    sb.add_cone_between(MAT_SILVER, (-0.34, 0.0, 0.0), (-0.38, 0.0, 0.0), radius=0.018)

    # Integer tick rings and standard real points -2, -1, 0, 1, 2
    for k in (-2, -1, 0, 1, 2):
        x = k * 0.13
        sb.add_torus(MAT_SILVER, major_radius=0.018, minor_radius=0.0035, center=(x, 0.0, 0.0), axis="x")
        sb.add_sphere(MAT_GOLD if k in (0, 1) else MAT_SILVER, (x, 0.0, 0.0), radius=0.015 if k in (0, 1) else 0.011)

    # Magnified Infinitesimal Microscope Stage floating above 0, connected by golden shadow beam
    halo_center = (0.0, 0.16, 0.0)
    sb.add_segment(MAT_GOLD, halo_center, (0.0, 0.0, 0.0), radius=0.005)
    sb.add_cone_between(MAT_GOLD, (0.0, 0.045, 0.0), (0.0, 0.015, 0.0), radius=0.013)

    # Outer microscope brass/gold lens ring + translucent Halo sphere hal(0) = I
    sb.add_torus(MAT_GOLD, major_radius=0.115, minor_radius=0.007, center=halo_center, axis="z")
    sb.add_sphere(MAT_HALO_GLASS, halo_center, radius=0.108, subdivisions=3)
    sb.add_sphere(MAT_GOLD, halo_center, radius=0.016)

    # Nested first-order (eps) and second-order (eps^2) infinitesimal orbits inside hal(0)
    sb.add_torus(MAT_CYAN, major_radius=0.068, minor_radius=0.0045, center=halo_center, axis="y")
    t_tilt = np.linspace(0, 2 * math.pi, 44)
    ring2 = np.column_stack(
        [
            0.036 * np.cos(t_tilt),
            0.16 + 0.036 * np.sin(t_tilt) * 0.55,
            0.036 * np.sin(t_tilt) * 0.83,
        ]
    )
    sb.add_polyline_tube(MAT_VIOLET, ring2, radius=0.0035, sections=10)
    # Sample hyperreal points 0 + eps, 0 - eps, 0 + eps^2
    sb.add_sphere(MAT_CYAN, (0.068, 0.16, 0.0), radius=0.011)
    sb.add_sphere(MAT_CYAN, (-0.068, 0.16, 0.0), radius=0.011)
    sb.add_sphere(MAT_VIOLET, (0.0, 0.18, 0.03), radius=0.009)

    # Secondary smaller halo around r = 1
    sb.add_sphere(MAT_HALO_GLASS, (0.13, 0.0, 0.0), radius=0.042, subdivisions=2)
    sb.add_sphere(MAT_CYAN, (0.155, 0.018, 0.015), radius=0.007)

    # Floating Infinite Galaxies gal(+omega) and gal(-omega) at +/- unlimited wings
    for sign, mat_gal in ((1.0, MAT_EMERALD), (-1.0, MAT_CORAL)):
        gx, gy, gz = sign * 0.36, 0.15, -0.06
        sb.add_torus(mat_gal, major_radius=0.065, minor_radius=0.004, center=(gx, gy, gz), axis="y")
        sb.add_segment(mat_gal, (gx - 0.055, gy, gz), (gx + 0.055, gy, gz), radius=0.004)
        for dx in (-0.038, 0.0, 0.038):
            sb.add_sphere(mat_gal, (gx + dx, gy, gz), radius=0.011 if dx == 0 else 0.008)
        # Telescope sightline from origin toward +/- omega galaxy
        sb.add_segment(MAT_SLATE, (sign * 0.12, 0.04, -0.01), (gx - sign * 0.06, gy - 0.02, gz), radius=0.0025)

    return sb


def build_ultrapower_germs() -> SceneBuilder:
    """Model 2: Three sequences over N funneling through a glowing Ultrafilter
    Lens F into hyperreal germs in R*: 1/n -> hal(0), n -> omega, and (1,0,1,0,...) -> 1."""
    sb = SceneBuilder("ultrapower_germs")

    # Sequence index spine along X from -0.36 to +0.06, Ultrafilter Lens at X = +0.12, R* column at X = +0.28
    sb.add_segment(MAT_SLATE, (-0.38, -0.14, 0.0), (0.10, -0.14, 0.0), radius=0.005)
    for idx in range(10):
        xn = -0.36 + idx * 0.048
        sb.add_sphere(MAT_SLATE, (xn, -0.14, 0.0), radius=0.007, subdivisions=1)

    # Glowing Golden Ultrafilter Lens F at X = 0.13
    lens_c = (0.13, 0.02, 0.0)
    sb.add_torus(MAT_GOLD, major_radius=0.16, minor_radius=0.008, center=lens_c, axis="x")
    sb.add_torus(MAT_VIOLET, major_radius=0.11, minor_radius=0.0045, center=lens_c, axis="x")

    # Vertical Hyperreal R* target axis at X = 0.29
    sb.add_segment(MAT_SILVER, (0.29, -0.18, 0.0), (0.29, 0.28, 0.0), radius=0.007)
    sb.add_cone_between(MAT_SILVER, (0.29, 0.28, 0.0), (0.29, 0.32, 0.0), radius=0.016)

    # Sequence 1 (Cyan): Harmonic spiral r_n = 1/(n+1) funneling into hal(0) at (0.29, -0.04, 0)
    t = np.linspace(0.0, 1.0, 48)
    xs = -0.36 + t * (0.29 - (-0.36))
    amp = 0.11 * np.exp(-2.6 * t) + 0.012
    ys = -0.04 + amp * np.sin(5.5 * math.pi * t)
    zs = amp * np.cos(5.5 * math.pi * t)
    pts_inf = np.column_stack([xs, ys, zs])
    sb.add_polyline_tube(MAT_CYAN, pts_inf, radius=0.0045, sections=10)
    for k in range(0, 42, 5):
        sb.add_sphere(MAT_CYAN, pts_inf[k], radius=0.009, subdivisions=2)
    sb.add_sphere(MAT_HALO_GLASS, (0.29, -0.04, 0.0), radius=0.045, subdivisions=3)
    sb.add_sphere(MAT_CYAN, (0.29, -0.04, 0.0), radius=0.013)

    # Sequence 2 (Coral): Unlimited sequence r_n = n rising smoothly to omega at (0.29, 0.24, 0)
    t2 = np.linspace(0.0, 1.0, 32)
    xs2 = -0.36 + t2 * (0.29 + 0.36)
    ys2 = -0.10 + 0.34 * (t2**1.55)
    zs2 = -0.05 * np.sin(math.pi * t2)
    pts_om = np.column_stack([xs2, ys2, zs2])
    sb.add_polyline_tube(MAT_CORAL, pts_om, radius=0.005, sections=10)
    for k in range(0, 30, 4):
        sb.add_sphere(MAT_CORAL, pts_om[k], radius=0.0095, subdivisions=2)
    sb.add_sphere(MAT_CORAL, (0.29, 0.24, 0.0), radius=0.018)

    # Sequence 3 (Emerald): Alternating (1, 0, 1, 0, ...) resolved by Ultrafilter F onto standard 1
    alt_pts = []
    for idx in range(10):
        xn = -0.36 + idx * 0.048
        yn = 0.09 if idx % 2 == 0 else -0.04
        zn = 0.06 if idx % 2 == 0 else -0.06
        sb.add_sphere(MAT_EMERALD if idx % 2 == 0 else MAT_SLATE, (xn, yn, zn), radius=0.010, subdivisions=2)
        if idx % 2 == 0:
            alt_pts.append([xn, yn, zn])
    alt_pts.append([0.13, 0.09, 0.03])
    alt_pts.append([0.29, 0.09, 0.0])
    sb.add_polyline_tube(MAT_EMERALD, np.asarray(alt_pts), radius=0.004, sections=10)
    sb.add_sphere(MAT_GOLD, (0.29, 0.09, 0.0), radius=0.015)

    return sb


def build_hyperfinite_riemann_loeb() -> SceneBuilder:
    """Model 3: Hyperfinite step-function Riemann columns of width dx = 1/N
    under a smooth curve f(x), paired with a Loeb uniform counting grid."""
    sb = SceneBuilder("hyperfinite_riemann_loeb")

    # Base Loeb hyperfinite grid platform
    sb.add_box(MAT_SLATE, extents=(0.66, 0.016, 0.28), center=(0.0, -0.15, 0.0))

    # Loeb grid ticks along front edge showing hyperfinite counting omega_k in {0, 1/N, ..., 1}
    n_bars = 28
    x0, x1 = -0.28, 0.28
    dx = (x1 - x0) / n_bars

    def f_curve(u: float) -> float:
        # Smooth positive wave on [0, 1]
        return 0.08 + 0.19 * math.sin(math.pi * u) ** 1.3 + 0.07 * math.cos(2.5 * math.pi * u) ** 2

    # Hyperfinite Riemann prism columns
    for i in range(n_bars):
        u = (i + 0.5) / n_bars
        xc = x0 + (i + 0.5) * dx
        h = f_curve(u)
        mat = MAT_CYAN if i % 4 != 0 else MAT_GOLD
        sb.add_box(
            mat,
            extents=(dx * 0.82, h, 0.075),
            center=(xc, -0.142 + h / 2.0, -0.035),
        )
        # Front Loeb counting node on [0, 1]
        sb.add_sphere(
            MAT_EMERALD if 0.22 <= u <= 0.72 else MAT_SILVER,
            (xc, -0.135, 0.095),
            radius=0.0065,
            subdivisions=1,
        )

    # Highlighted Loeb measurable event A subseteq [0, 1] bar in front
    sb.add_box(MAT_EMERALD, extents=(0.50 * (x1 - x0), 0.012, 0.032), center=(-0.016, -0.128, 0.095))

    # Smooth standard shadow curve y = f(x) arching cleanly over the hyperfinite columns
    us = np.linspace(0.0, 1.0, 64)
    curve_pts = np.column_stack(
        [
            x0 + us * (x1 - x0),
            np.array([-0.142 + f_curve(float(u)) + 0.008 for u in us]),
            np.full_like(us, -0.035),
        ]
    )
    sb.add_polyline_tube(MAT_CORAL, curve_pts, radius=0.0065, sections=12)

    # Translucent golden shadow shell representing sh(sum f(x_i) dx) = integral_0^1 f(x) dx
    for i in range(0, n_bars, 2):
        u = (i + 1.0) / n_bars
        xc = x0 + (i + 1.0) * dx
        h = f_curve(min(u, 1.0))
        sb.add_box(
            MAT_GOLD_GLASS,
            extents=(dx * 1.96, h, 0.045),
            center=(xc, -0.142 + h / 2.0, 0.032),
        )

    return sb


def build_superstructure_cone() -> SceneBuilder:
    """Model 4: Dual cumulative hierarchy cones V(R) and V(*R) connected by
    luminous *-transfer arcs, showing internal *V(R) inside external V(*R)."""
    sb = SceneBuilder("superstructure_cone")

    left_x, right_x = -0.22, 0.22
    levels_y = [-0.14, -0.03, 0.09, 0.22]
    radii_std = [0.035, 0.070, 0.105, 0.140]

    # Left cone: Standard Superstructure V_n(R)
    sb.add_sphere(MAT_GOLD, (left_x, -0.17, 0.0), radius=0.018)
    for lvl, (y, r) in enumerate(zip(levels_y, radii_std)):
        sb.add_torus(MAT_GOLD if lvl < 3 else MAT_SILVER, major_radius=r, minor_radius=0.0055, center=(left_x, y, 0.0), axis="y")
    for angle in np.linspace(0, 2 * math.pi, 6, endpoint=False):
        p0 = (left_x + radii_std[0] * math.cos(angle), levels_y[0], radii_std[0] * math.sin(angle))
        p1 = (left_x + radii_std[-1] * math.cos(angle), levels_y[-1], radii_std[-1] * math.sin(angle))
        sb.add_segment(MAT_SILVER, p0, p1, radius=0.003)

    # Right cone: Nonstandard Superstructure V(*R) = Internal *V(R) core + External outer cage
    sb.add_sphere(MAT_CYAN, (right_x, -0.17, 0.0), radius=0.020)
    for y, r in zip(levels_y, radii_std):
        # Inner internal sub-cone *V_n(R)
        r_int = r * 0.85
        sb.add_torus(MAT_CYAN, major_radius=r_int, minor_radius=0.0055, center=(right_x, y, 0.0), axis="y")
        # Outer full superstructure V_n(*R) containing external sets (R, N, L, I, Loeb)
        r_ext = r * 1.25
        sb.add_torus(MAT_VIOLET, major_radius=r_ext, minor_radius=0.0038, center=(right_x, y, 0.0), axis="y")

    # Translucent sapphire cone shell marking the Internal/External boundary
    cone_mesh = trimesh.creation.cone(radius=0.125, height=0.38, sections=32)
    rot = trimesh.transformations.rotation_matrix(-math.pi / 2.0, [1, 0, 0])
    cone_mesh.apply_transform(rot)
    # Invert so narrow base is at bottom, wide mouth at top: rotate 180 deg around Z
    flip = trimesh.transformations.rotation_matrix(math.pi, [0, 0, 1])
    cone_mesh.apply_transform(flip)
    cone_mesh.apply_translation((right_x, 0.22, 0.0))
    sb.add(MAT_HALO_GLASS, cone_mesh)

    # External entity satellites orbiting outside *V(R) inside V(*R)
    for ang, y_ext in ((0.4, 0.09), (2.3, 0.16), (4.5, 0.22)):
        rx = right_x + 0.155 * math.cos(ang)
        rz = 0.155 * math.sin(ang)
        sb.add_sphere(MAT_CORAL, (rx, y_ext, rz), radius=0.011)

    # Luminous *-transform transfer bridges from V_n(R) -> *V_n(R)
    for y, r in zip(levels_y[1:], radii_std[1:]):
        ts = np.linspace(0.0, 1.0, 28)
        arc_x = (left_x + r * 0.7) * (1 - ts) + (right_x - r * 0.65) * ts
        arc_y = y + 0.085 * np.sin(math.pi * ts)
        arc_z = -0.03 * np.sin(math.pi * ts)
        arc = np.column_stack([arc_x, arc_y, arc_z])
        sb.add_polyline_tube(MAT_GOLD, arc, radius=0.0042, sections=10)
        sb.add_cone_between(MAT_GOLD, arc[-2], arc[-1], radius=0.011)

    return sb


def build_padic_stone_hull() -> SceneBuilder:
    """Model 5: 3-adic valuation fractal tree inside a translucent Nonstandard Hull
    unit sphere M_fin / ~, tangent to a Hyperfinite Hahn-Banach hyperplane."""
    sb = SceneBuilder("padic_stone_hull")

    # Recursive 3-adic branching tree (root -> 3 -> 9 -> 27 coset balls)
    root = np.array([0.0, -0.18, 0.0])
    sb.add_sphere(MAT_GOLD, root, radius=0.020)

    level1_r = 0.11
    for i in range(3):
        a1 = i * (2 * math.pi / 3.0)
        p1 = np.array([level1_r * math.cos(a1), -0.05, level1_r * math.sin(a1)])
        sb.add_segment(MAT_GOLD, root, p1, radius=0.0065)
        sb.add_sphere(MAT_CYAN, p1, radius=0.014)

        level2_r = 0.058
        for j in range(3):
            a2 = a1 + (j - 1) * 0.85
            p2 = np.array([p1[0] + level2_r * math.cos(a2), 0.07, p1[2] + level2_r * math.sin(a2)])
            sb.add_segment(MAT_CYAN, p1, p2, radius=0.0042)
            sb.add_sphere(MAT_EMERALD, p2, radius=0.0095)

            level3_r = 0.028
            for k in range(3):
                a3 = a2 + (k - 1) * 0.9
                p3 = np.array([p2[0] + level3_r * math.cos(a3), 0.16, p2[2] + level3_r * math.sin(a3)])
                sb.add_segment(MAT_VIOLET, p2, p3, radius=0.0026, sections=8)
                sb.add_sphere(MAT_CORAL, p3, radius=0.0055, subdivisions=1)

    # Translucent Nonstandard Hull Unit Ball shell around the fractal tree
    sb.add_sphere(MAT_HALO_GLASS, (0.0, 0.02, 0.0), radius=0.205, subdivisions=3)
    sb.add_torus(MAT_SILVER, major_radius=0.205, minor_radius=0.0038, center=(0.0, 0.02, 0.0), axis="y")

    # Hyperfinite Hahn-Banach Supporting Hyperplane tangent at top-right of unit sphere
    plane = trimesh.creation.box(extents=(0.28, 0.006, 0.24))
    rot = trimesh.transformations.rotation_matrix(-0.42, [0, 0, 1])
    plane.apply_transform(rot)
    # Normal direction of rotated Y-normal box is (sin(0.42), cos(0.42), 0)
    n_vec = np.array([math.sin(0.42), math.cos(0.42), 0.0])
    tangent_pt = np.array([0.0, 0.02, 0.0]) + 0.206 * n_vec
    plane.apply_translation(tangent_pt)
    sb.add(MAT_GOLD_GLASS, plane)
    sb.add_sphere(MAT_GOLD, tangent_pt, radius=0.013)
    # Normal functional vector f(x) = 1 at tangency point
    sb.add_segment(MAT_GOLD, tangent_pt, tangent_pt + 0.075 * n_vec, radius=0.0045)
    sb.add_cone_between(MAT_GOLD, tangent_pt + 0.075 * n_vec, tangent_pt + 0.102 * n_vec, radius=0.012)

    return sb


# ---------------------------------------------------------------------------
# Bespoke Mathematical SVG Diagrams (Retina-crisp, dark/light-friendly)
# ---------------------------------------------------------------------------

SVG_SHARED_DEFS = """
  <defs>
    <linearGradient id="bgCard" x1="0" y1="0" x2="1" y2="1">
      <stop offset="0%" stop-color="#0f172a"/>
      <stop offset="100%" stop-color="#1e293b"/>
    </linearGradient>
    <linearGradient id="goldBeam" x1="0" y1="0" x2="0" y2="1">
      <stop offset="0%" stop-color="#fbbf24" stop-opacity="0.45"/>
      <stop offset="100%" stop-color="#fbbf24" stop-opacity="0.06"/>
    </linearGradient>
    <linearGradient id="cyanGlow" x1="0" y1="0" x2="1" y2="1">
      <stop offset="0%" stop-color="#38bdf8" stop-opacity="0.32"/>
      <stop offset="100%" stop-color="#818cf8" stop-opacity="0.12"/>
    </linearGradient>
    <linearGradient id="emeraldGrad" x1="0" y1="0" x2="1" y2="0">
      <stop offset="0%" stop-color="#34d399"/>
      <stop offset="100%" stop-color="#38bdf8"/>
    </linearGradient>
    <marker id="arrowSilver" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
      <path d="M 0 1 L 10 5 L 0 9 z" fill="#cbd5e1"/>
    </marker>
    <marker id="arrowGold" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
      <path d="M 0 1 L 10 5 L 0 9 z" fill="#fbbf24"/>
    </marker>
    <marker id="arrowCyan" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
      <path d="M 0 1 L 10 5 L 0 9 z" fill="#38bdf8"/>
    </marker>
  </defs>
"""


def write_svgs() -> list[Path]:
    DIAGRAMS_DIR.mkdir(parents=True, exist_ok=True)
    written: list[Path] = []

    # 0. Site Logo
    logo_path = STATIC_DIR / "logo.svg"
    logo_path.write_text(
        """<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 64 64" width="64" height="64">
  <defs>
    <linearGradient id="g1" x1="0" y1="0" x2="1" y2="1">
      <stop offset="0%" stop-color="#38bdf8"/>
      <stop offset="100%" stop-color="#818cf8"/>
    </linearGradient>
  </defs>
  <rect x="4" y="4" width="56" height="56" rx="14" fill="#0f172a" stroke="#334155" stroke-width="2"/>
  <circle cx="32" cy="32" r="19" fill="none" stroke="url(#g1)" stroke-width="2.5" stroke-dasharray="4 3"/>
  <ellipse cx="32" cy="32" rx="22" ry="9" transform="rotate(-24 32 32)" fill="none" stroke="#fbbf24" stroke-width="2"/>
  <circle cx="32" cy="32" r="5" fill="#fbbf24"/>
  <circle cx="48" cy="25" r="3" fill="#38bdf8"/>
</svg>
""",
        encoding="utf-8",
    )
    written.append(logo_path)

    # 1. Ch 1 & 5: Infinitesimal Microscope & Infinite Telescope
    p1 = DIAGRAMS_DIR / "ch01_microscope_telescope.svg"
    p1.write_text(
        f"""<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 920 430">
  {SVG_SHARED_DEFS}
  <rect width="920" height="430" rx="20" fill="url(#bgCard)"/>
  <text x="36" y="42" fill="#f8fafc" font-family="system-ui, -apple-system, sans-serif" font-size="20" font-weight="700">Anatomy of the Hyperreal Line ℝ* — Galaxies, Halos &amp; the Shadow Map</text>
  <text x="36" y="66" fill="#94a3b8" font-family="system-ui, -apple-system, sans-serif" font-size="13">Every limited hyperreal x ∈ 𝕃 decomposes uniquely as x = sh(x) + ε with sh(x) ∈ ℝ and ε ∈ 𝕀 = hal(0)</text>

  <!-- Top Band: Infinite Telescope -->
  <rect x="36" y="86" width="848" height="96" rx="14" fill="#0b1220" stroke="#334155" stroke-width="1.2"/>
  <text x="54" y="109" fill="#34d399" font-family="system-ui, sans-serif" font-size="12" font-weight="700" letter-spacing="0.06em">INFINITE TELESCOPE (ℝ* = 𝕃_neg ⊔ 𝕃 ⊔ 𝕃_pos)</text>
  <line x1="66" y1="146" x2="854" y2="146" stroke="#64748b" stroke-width="2" marker-start="url(#arrowSilver)" marker-end="url(#arrowSilver)"/>
  <!-- Negative galaxy gal(-ω) -->
  <rect x="92" y="126" width="140" height="40" rx="20" fill="#ef4444" fill-opacity="0.14" stroke="#f87171" stroke-dasharray="4 3"/>
  <circle cx="162" cy="146" r="5" fill="#f87171"/>
  <text x="162" y="120" text-anchor="middle" fill="#fca5a5" font-family="ui-monospace, monospace" font-size="12">gal(−ω) = −ω + 𝕃</text>
  <text x="162" y="162" text-anchor="middle" fill="#fecaca" font-family="ui-monospace, monospace" font-size="11">−ω−1   −ω   −ω+1</text>

  <!-- Principal Galaxy L = gal(0) -->
  <rect x="310" y="122" width="300" height="48" rx="24" fill="#38bdf8" fill-opacity="0.13" stroke="#38bdf8" stroke-width="1.6"/>
  <text x="460" y="116" text-anchor="middle" fill="#7dd3fc" font-family="ui-monospace, monospace" font-size="12" font-weight="700">Principal Galaxy 𝕃 = gal(0) (Limited Hyperreals)</text>
  <circle cx="360" cy="146" r="4" fill="#cbd5e1"/><text x="360" y="164" text-anchor="middle" fill="#cbd5e1" font-family="ui-monospace, monospace" font-size="11">−1</text>
  <circle cx="430" cy="146" r="5.5" fill="#fbbf24"/><text x="430" y="164" text-anchor="middle" fill="#fde68a" font-family="ui-monospace, monospace" font-size="11">0</text>
  <circle cx="505" cy="146" r="5.5" fill="#fbbf24"/><text x="505" y="164" text-anchor="middle" fill="#fde68a" font-family="ui-monospace, monospace" font-size="11">r</text>
  <circle cx="565" cy="146" r="4" fill="#cbd5e1"/><text x="565" y="164" text-anchor="middle" fill="#cbd5e1" font-family="ui-monospace, monospace" font-size="11">2</text>

  <!-- Positive galaxy gal(+ω) -->
  <rect x="688" y="126" width="144" height="40" rx="20" fill="#10b981" fill-opacity="0.14" stroke="#34d399" stroke-dasharray="4 3"/>
  <circle cx="760" cy="146" r="5" fill="#34d399"/>
  <text x="760" y="120" text-anchor="middle" fill="#6ee7b7" font-family="ui-monospace, monospace" font-size="12">gal(+ω) = ω + 𝕃</text>
  <text x="760" y="162" text-anchor="middle" fill="#a7f3d0" font-family="ui-monospace, monospace" font-size="11">ω−1    ω    ω+1</text>

  <!-- Magnifying cone from r into Infinitesimal Microscope -->
  <polygon points="497,150 513,150 675,232 245,232" fill="url(#goldBeam)"/>
  <line x1="497" y1="150" x2="245" y2="232" stroke="#fbbf24" stroke-opacity="0.6" stroke-dasharray="5 4"/>
  <line x1="513" y1="150" x2="675" y2="232" stroke="#fbbf24" stroke-opacity="0.6" stroke-dasharray="5 4"/>

  <!-- Bottom Left: Infinitesimal Microscope on hal(r) -->
  <rect x="36" y="220" width="664" height="182" rx="16" fill="#0b1220" stroke="#fbbf24" stroke-opacity="0.65" stroke-width="1.5"/>
  <text x="56" y="247" fill="#fbbf24" font-family="system-ui, sans-serif" font-size="12" font-weight="700" letter-spacing="0.06em">INFINITESIMAL MICROSCOPE — HALO hal(r) = &#123; x ∈ ℝ* : x ≈ r &#125;</text>
  <ellipse cx="368" cy="316" rx="276" ry="56" fill="url(#cyanGlow)" stroke="#38bdf8" stroke-width="1.5"/>
  <ellipse cx="368" cy="316" rx="92" ry="30" fill="#818cf8" fill-opacity="0.16" stroke="#a5b4fc" stroke-dasharray="4 3"/>
  <line x1="72" y1="316" x2="664" y2="316" stroke="#94a3b8" stroke-width="2"/>

  <!-- Points inside hal(r) -->
  <circle cx="168" cy="316" r="4.5" fill="#38bdf8"/><text x="168" y="340" text-anchor="middle" fill="#7dd3fc" font-family="ui-monospace, monospace" font-size="12">r − 2ε</text>
  <circle cx="246" cy="316" r="4.5" fill="#38bdf8"/><text x="246" y="340" text-anchor="middle" fill="#7dd3fc" font-family="ui-monospace, monospace" font-size="12">r − ε</text>
  <circle cx="368" cy="316" r="7" fill="#fbbf24"/><text x="368" y="299" text-anchor="middle" fill="#fde68a" font-family="ui-monospace, monospace" font-size="13" font-weight="700">r = sh(x)</text>
  <circle cx="422" cy="316" r="4" fill="#c4b5fd"/><text x="422" y="340" text-anchor="middle" fill="#ddd6fe" font-family="ui-monospace, monospace" font-size="11">r + ε²</text>
  <circle cx="490" cy="316" r="5" fill="#38bdf8"/><text x="490" y="340" text-anchor="middle" fill="#7dd3fc" font-family="ui-monospace, monospace" font-size="12">x = r + ε</text>
  <circle cx="568" cy="316" r="4.5" fill="#38bdf8"/><text x="568" y="340" text-anchor="middle" fill="#7dd3fc" font-family="ui-monospace, monospace" font-size="12">r + 2ε</text>
  <text x="368" y="388" text-anchor="middle" fill="#94a3b8" font-family="system-ui, sans-serif" font-size="12">Second-order halo: ε² / ε = ε ≈ 0, while Dedekind completeness pushes the entire halo onto a single shadow r ∈ ℝ</text>

  <!-- Bottom Right: Quotient Ring Isomorphism Card -->
  <rect x="718" y="220" width="166" height="182" rx="16" fill="#111c33" stroke="#475569" stroke-width="1.2"/>
  <text x="801" y="250" text-anchor="middle" fill="#7dd3fc" font-family="system-ui, sans-serif" font-size="12" font-weight="700">SHADOW QUOTIENT</text>
  <text x="801" y="286" text-anchor="middle" fill="#f8fafc" font-family="ui-monospace, monospace" font-size="18" font-weight="700">𝕃 / 𝕀 ≃+* ℝ</text>
  <line x1="740" y1="304" x2="862" y2="304" stroke="#334155"/>
  <text x="801" y="328" text-anchor="middle" fill="#cbd5e1" font-family="ui-monospace, monospace" font-size="12">𝕃 : valuation subring</text>
  <text x="801" y="350" text-anchor="middle" fill="#cbd5e1" font-family="ui-monospace, monospace" font-size="12">𝕀 : maximal ideal</text>
  <text x="801" y="376" text-anchor="middle" fill="#fbbf24" font-family="ui-monospace, monospace" font-size="12">ker(shadow) = 𝕀</text>
</svg>
""",
        encoding="utf-8",
    )
    written.append(p1)

    # 2. Ch 2–4: Ultrapower Sequence-to-Germ Collapse & Łoś Transfer
    p2 = DIAGRAMS_DIR / "ch03_ultrapower_filter.svg"
    p2.write_text(
        f"""<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 920 390">
  {SVG_SHARED_DEFS}
  <rect width="920" height="390" rx="20" fill="url(#bgCard)"/>
  <text x="36" y="42" fill="#f8fafc" font-family="system-ui, -apple-system, sans-serif" font-size="20" font-weight="700">Ultrapower Construction ℝ* = ℝ^ℕ / ℱ &amp; Łoś Index-wise Transfer</text>
  <text x="36" y="66" fill="#94a3b8" font-family="system-ui, -apple-system, sans-serif" font-size="13">Free ultrafilter ℱ ⊇ cofinite sets acts as a 0–1 voting measure on subsets of ℕ without naming a dictator index</text>

  <!-- Left: Sequence table over N -->
  <rect x="36" y="88" width="450" height="270" rx="16" fill="#0b1220" stroke="#334155" stroke-width="1.2"/>
  <text x="56" y="114" fill="#7dd3fc" font-family="system-ui, sans-serif" font-size="12" font-weight="700" letter-spacing="0.05em">REAL SEQUENCES IN ℝ^ℕ (INDEXED BY n ∈ ℕ)</text>

  <text x="64" y="146" fill="#94a3b8" font-family="ui-monospace, monospace" font-size="12">n     =</text>
  <text x="140" y="146" fill="#cbd5e1" font-family="ui-monospace, monospace" font-size="12">0     1      2      3      4     5    ⋯</text>

  <!-- Sequence omega = (0,1,2,3,...) -->
  <rect x="52" y="162" width="418" height="38" rx="9" fill="#f87171" fill-opacity="0.11" stroke="#f87171" stroke-opacity="0.4"/>
  <text x="64" y="186" fill="#fca5a5" font-family="ui-monospace, monospace" font-size="13" font-weight="700">ω_n   =</text>
  <text x="140" y="186" fill="#fecaca" font-family="ui-monospace, monospace" font-size="13">0     1      2      3      4     5    → +∞</text>

  <!-- Sequence eps = (1, 1/2, 1/3, ...) -->
  <rect x="52" y="212" width="418" height="38" rx="9" fill="#38bdf8" fill-opacity="0.12" stroke="#38bdf8" stroke-opacity="0.45"/>
  <text x="64" y="236" fill="#7dd3fc" font-family="ui-monospace, monospace" font-size="13" font-weight="700">ε_n   =</text>
  <text x="140" y="236" fill="#bae6fd" font-family="ui-monospace, monospace" font-size="13">1    1/2    1/3    1/4    1/5   1/6   → 0⁺</text>

  <!-- Alternating sequence (1, 0, 1, 0, ...) -->
  <rect x="52" y="262" width="418" height="38" rx="9" fill="#a78bfa" fill-opacity="0.12" stroke="#a78bfa" stroke-opacity="0.45"/>
  <text x="64" y="286" fill="#ddd6fe" font-family="ui-monospace, monospace" font-size="13" font-weight="700">a_n   =</text>
  <text x="140" y="286" fill="#ede9fe" font-family="ui-monospace, monospace" font-size="13">1     0      1      0      1     0    (2ℕ vs 2ℕ+1)</text>

  <text x="64" y="334" fill="#fbbf24" font-family="ui-monospace, monospace" font-size="12">⟦ [r] &lt; [s] ⟧  ⟺  &#123; n ∈ ℕ : r_n &lt; s_n &#125; ∈ ℱ</text>

  <!-- Center: Ultrafilter Lens -->
  <ellipse cx="585" cy="223" rx="52" ry="118" fill="url(#goldBeam)" stroke="#fbbf24" stroke-width="2"/>
  <text x="585" y="148" text-anchor="middle" fill="#fde68a" font-family="system-ui, sans-serif" font-size="13" font-weight="700">Free</text>
  <text x="585" y="166" text-anchor="middle" fill="#fde68a" font-family="system-ui, sans-serif" font-size="13" font-weight="700">Ultrafilter</text>
  <text x="585" y="196" text-anchor="middle" fill="#fbbf24" font-family="ui-monospace, monospace" font-size="22" font-weight="700">ℱ</text>
  <text x="585" y="230" text-anchor="middle" fill="#e2e8f0" font-family="ui-monospace, monospace" font-size="11">A ∈ ℱ or Aᶜ ∈ ℱ</text>
  <text x="585" y="250" text-anchor="middle" fill="#94a3b8" font-family="ui-monospace, monospace" font-size="11">finite ∉ ℱ</text>
  <text x="585" y="270" text-anchor="middle" fill="#94a3b8" font-family="ui-monospace, monospace" font-size="11">(Zorn's Lemma)</text>

  <!-- Arrows through lens to germs in R* -->
  <path d="M 472 181 C 530 181, 640 148, 696 142" fill="none" stroke="#f87171" stroke-width="2.4" marker-end="url(#arrowSilver)"/>
  <path d="M 472 231 C 530 231, 640 223, 696 223" fill="none" stroke="#38bdf8" stroke-width="2.4" marker-end="url(#arrowCyan)"/>
  <path d="M 472 281 C 530 281, 640 296, 696 304" fill="none" stroke="#a78bfa" stroke-width="2.4" marker-end="url(#arrowGold)"/>

  <!-- Right: Resulting Germs in R* -->
  <rect x="698" y="88" width="186" height="270" rx="16" fill="#0b1220" stroke="#334155" stroke-width="1.2"/>
  <text x="791" y="114" text-anchor="middle" fill="#34d399" font-family="system-ui, sans-serif" font-size="12" font-weight="700">GERMS IN ℝ*</text>

  <rect x="716" y="124" width="150" height="52" rx="10" fill="#ef4444" fill-opacity="0.14" stroke="#f87171"/>
  <text x="791" y="146" text-anchor="middle" fill="#fecaca" font-family="ui-monospace, monospace" font-size="13" font-weight="700">ω = [n] &gt; ℝ</text>
  <text x="791" y="165" text-anchor="middle" fill="#fca5a5" font-family="system-ui, sans-serif" font-size="11">Positive unlimited</text>

  <rect x="716" y="196" width="150" height="54" rx="10" fill="#38bdf8" fill-opacity="0.14" stroke="#38bdf8"/>
  <text x="791" y="218" text-anchor="middle" fill="#bae6fd" font-family="ui-monospace, monospace" font-size="13" font-weight="700">ε = [1/n] ∈ 𝕀</text>
  <text x="791" y="238" text-anchor="middle" fill="#7dd3fc" font-family="system-ui, sans-serif" font-size="11">0 &lt; ε &lt; r (∀ r &gt; 0)</text>

  <rect x="716" y="272" width="150" height="66" rx="10" fill="#fbbf24" fill-opacity="0.12" stroke="#fbbf24"/>
  <text x="791" y="294" text-anchor="middle" fill="#fde68a" font-family="ui-monospace, monospace" font-size="13" font-weight="700">[a] = 1 or 0</text>
  <text x="791" y="313" text-anchor="middle" fill="#cbd5e1" font-family="system-ui, sans-serif" font-size="11">No zero divisors!</text>
  <text x="791" y="328" text-anchor="middle" fill="#94a3b8" font-family="ui-monospace, monospace" font-size="10">a·(1−a) = 0 ⟹ ℝ* field</text>
</svg>
""",
        encoding="utf-8",
    )
    written.append(p2)

    # 3. Ch 8–9: Incremental Equation & Shadow Riemann Sums
    p3 = DIAGRAMS_DIR / "ch08_incremental_calculus.svg"
    p3.write_text(
        f"""<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 920 400">
  {SVG_SHARED_DEFS}
  <rect width="920" height="400" rx="20" fill="url(#bgCard)"/>
  <text x="36" y="42" fill="#f8fafc" font-family="system-ui, -apple-system, sans-serif" font-size="20" font-weight="700">Infinitesimal Calculus — Incremental Equation &amp; Hyperfinite Riemann Sums</text>
  <text x="36" y="66" fill="#94a3b8" font-family="system-ui, -apple-system, sans-serif" font-size="13">Derivatives become exact ratios modulo 𝕀, and definite integrals become shadows of hyperfinite sums</text>

  <!-- Left Panel: Incremental Equation -->
  <rect x="36" y="88" width="424" height="284" rx="16" fill="#0b1220" stroke="#334155" stroke-width="1.2"/>
  <text x="56" y="114" fill="#fbbf24" font-family="system-ui, sans-serif" font-size="12" font-weight="700">CH. 8 · INCREMENTAL EQUATION Δf = f'(x)Δx + ηΔx</text>

  <!-- Axes & Curve -->
  <line x1="74" y1="326" x2="424" y2="326" stroke="#64748b" stroke-width="1.5"/>
  <line x1="74" y1="326" x2="74" y2="136" stroke="#64748b" stroke-width="1.5"/>
  <path d="M 96 304 Q 230 282, 378 152" fill="none" stroke="#38bdf8" stroke-width="3"/>
  <!-- Tangent line from (152, 286) to (352, 200) -->
  <line x1="152" y1="286" x2="352" y2="200" stroke="#fbbf24" stroke-width="2" stroke-dasharray="6 4"/>
  <!-- Vertical/horizontal Δx and Δf -->
  <line x1="152" y1="286" x2="352" y2="286" stroke="#94a3b8" stroke-dasharray="3 3"/>
  <line x1="352" y1="286" x2="352" y2="173" stroke="#94a3b8" stroke-dasharray="3 3"/>
  <!-- Braces/segments -->
  <line x1="360" y1="286" x2="360" y2="200" stroke="#fbbf24" stroke-width="3"/>
  <text x="372" y="248" fill="#fde68a" font-family="ui-monospace, monospace" font-size="12">f'(x)Δx</text>
  <line x1="360" y1="200" x2="360" y2="173" stroke="#f472b6" stroke-width="3"/>
  <text x="372" y="190" fill="#f9a8d4" font-family="ui-monospace, monospace" font-size="12">η·Δx (η ≈ 0)</text>

  <circle cx="152" cy="286" r="5.5" fill="#fbbf24"/>
  <text x="146" y="308" text-anchor="middle" fill="#fde68a" font-family="ui-monospace, monospace" font-size="12">(x, *f(x))</text>
  <circle cx="352" cy="173" r="5.5" fill="#38bdf8"/>
  <text x="252" y="304" text-anchor="middle" fill="#cbd5e1" font-family="ui-monospace, monospace" font-size="12">Δx ∈ 𝕀 \\ &#123;0&#125;</text>
  <text x="248" y="352" text-anchor="middle" fill="#7dd3fc" font-family="ui-monospace, monospace" font-size="12">sh(Δf / Δx) = sh(f'(x) + η) = f'(x)</text>

  <!-- Right Panel: Shadow Riemann Integral -->
  <rect x="476" y="88" width="408" height="284" rx="16" fill="#0b1220" stroke="#334155" stroke-width="1.2"/>
  <text x="496" y="114" fill="#34d399" font-family="system-ui, sans-serif" font-size="12" font-weight="700">CH. 9 · HYPERFINITE RIEMANN SUM S(f, a, b, dx)</text>

  <line x1="510" y1="322" x2="854" y2="322" stroke="#64748b" stroke-width="1.5"/>
  <!-- 16 fine Riemann bars -->
  {"".join(
      f'<rect x="{524 + i * 19}" y="{int(322 - (70 + 88 * math.sin(math.pi * (i + 0.5) / 16)))}" width="17" height="{int(70 + 88 * math.sin(math.pi * (i + 0.5) / 16))}" fill="#38bdf8" fill-opacity="0.26" stroke="#38bdf8" stroke-width="1"/>'
      for i in range(16)
  )}
  <path d="M 524 252 Q 676 96, 828 252" fill="none" stroke="#fbbf24" stroke-width="3"/>
  <text x="524" y="340" text-anchor="middle" fill="#cbd5e1" font-family="ui-monospace, monospace" font-size="12">a</text>
  <text x="828" y="340" text-anchor="middle" fill="#cbd5e1" font-family="ui-monospace, monospace" font-size="12">b</text>
  <text x="676" y="340" text-anchor="middle" fill="#7dd3fc" font-family="ui-monospace, monospace" font-size="11">N = ⌊(b−a)/dx⌋ hyperfinite strips (dx ≈ 0⁺)</text>
  <text x="676" y="360" text-anchor="middle" fill="#fde68a" font-family="ui-monospace, monospace" font-size="12">∫_a^b f(x) dx = sh( ∑_&#123;k=0&#125;^&#123;N−1&#125; *f(x_k) · dx )</text>
</svg>
""",
        encoding="utf-8",
    )
    written.append(p3)

    # 4. Ch 10: Robinson's Nonstandard Topology & Compactness
    p4 = DIAGRAMS_DIR / "ch10_halo_topology.svg"
    p4.write_text(
        f"""<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 920 360">
  {SVG_SHARED_DEFS}
  <rect width="920" height="360" rx="20" fill="url(#bgCard)"/>
  <text x="36" y="42" fill="#f8fafc" font-family="system-ui, -apple-system, sans-serif" font-size="20" font-weight="700">Robinson's Nonstandard Topology — Open, Closed &amp; Compact via Halos</text>
  <text x="36" y="66" fill="#94a3b8" font-family="system-ui, -apple-system, sans-serif" font-size="13">Quantifier alternation over ε-balls collapses to single-step halo membership in ℝ*</text>

  <!-- Card 1: Open -->
  <rect x="36" y="92" width="272" height="236" rx="16" fill="#0b1220" stroke="#38bdf8" stroke-opacity="0.55"/>
  <text x="172" y="120" text-anchor="middle" fill="#7dd3fc" font-family="system-ui, sans-serif" font-size="13" font-weight="700">OPEN SET G ⊆ ℝ</text>
  <rect x="64" y="150" width="216" height="68" rx="34" fill="#38bdf8" fill-opacity="0.12" stroke="#38bdf8"/>
  <circle cx="172" cy="184" r="24" fill="#fbbf24" fill-opacity="0.20" stroke="#fbbf24" stroke-dasharray="4 3"/>
  <circle cx="172" cy="184" r="5" fill="#fbbf24"/>
  <text x="172" y="172" text-anchor="middle" fill="#fde68a" font-family="ui-monospace, monospace" font-size="11">hal(r) ⊆ *G</text>
  <text x="172" y="252" text-anchor="middle" fill="#e2e8f0" font-family="ui-monospace, monospace" font-size="12">∀ r ∈ G, hal(r) ⊆ *G</text>
  <text x="172" y="280" text-anchor="middle" fill="#94a3b8" font-family="system-ui, sans-serif" font-size="12">Every point infinitesimally</text>
  <text x="172" y="298" text-anchor="middle" fill="#94a3b8" font-family="system-ui, sans-serif" font-size="12">close to r stays inside *G</text>

  <!-- Card 2: Closed -->
  <rect x="324" y="92" width="272" height="236" rx="16" fill="#0b1220" stroke="#a78bfa" stroke-opacity="0.55"/>
  <text x="460" y="120" text-anchor="middle" fill="#c4b5fd" font-family="system-ui, sans-serif" font-size="13" font-weight="700">CLOSED SET F ⊆ ℝ</text>
  <rect x="356" y="150" width="208" height="68" rx="12" fill="#8b5cf6" fill-opacity="0.14" stroke="#a78bfa"/>
  <circle cx="424" cy="176" r="5" fill="#38bdf8"/>
  <text x="424" y="164" text-anchor="middle" fill="#bae6fd" font-family="ui-monospace, monospace" font-size="11">x ∈ *F ∩ 𝕃</text>
  <path d="M 432 180 L 488 194" stroke="#fbbf24" stroke-width="2" marker-end="url(#arrowGold)"/>
  <circle cx="498" cy="196" r="6" fill="#fbbf24"/>
  <text x="502" y="182" text-anchor="middle" fill="#fde68a" font-family="ui-monospace, monospace" font-size="11">sh(x) ∈ F</text>
  <text x="460" y="252" text-anchor="middle" fill="#e2e8f0" font-family="ui-monospace, monospace" font-size="12">x ∈ *F ∩ 𝕃 ⟹ sh(x) ∈ F</text>
  <text x="460" y="280" text-anchor="middle" fill="#94a3b8" font-family="system-ui, sans-serif" font-size="12">Shadows of limited points</text>
  <text x="460" y="298" text-anchor="middle" fill="#94a3b8" font-family="system-ui, sans-serif" font-size="12">cannot escape F</text>

  <!-- Card 3: Robinson Compactness -->
  <rect x="612" y="92" width="272" height="236" rx="16" fill="#0b1220" stroke="#34d399" stroke-opacity="0.6"/>
  <text x="748" y="120" text-anchor="middle" fill="#6ee7b7" font-family="system-ui, sans-serif" font-size="13" font-weight="700">COMPACT SET K ⊆ ℝ</text>
  <rect x="640" y="150" width="216" height="68" rx="34" fill="#10b981" fill-opacity="0.14" stroke="#34d399"/>
  <circle cx="690" cy="184" r="22" fill="#34d399" fill-opacity="0.18" stroke="#6ee7b7" stroke-dasharray="3 2"/>
  <circle cx="748" cy="184" r="22" fill="#34d399" fill-opacity="0.18" stroke="#6ee7b7" stroke-dasharray="3 2"/>
  <circle cx="806" cy="184" r="22" fill="#34d399" fill-opacity="0.18" stroke="#6ee7b7" stroke-dasharray="3 2"/>
  <text x="748" y="252" text-anchor="middle" fill="#e2e8f0" font-family="ui-monospace, monospace" font-size="12">∀ x ∈ *K, ∃ r ∈ K, x ≈ r</text>
  <text x="748" y="280" text-anchor="middle" fill="#fca5a5" font-family="ui-monospace, monospace" font-size="11">(0, 1] fails: ε ∈ *(0,1], sh(ε)=0∉(0,1]</text>
  <text x="748" y="300" text-anchor="middle" fill="#6ee7b7" font-family="system-ui, sans-serif" font-size="11">Heine–Cantor &amp; EVT become 6-line proofs!</text>
</svg>
""",
        encoding="utf-8",
    )
    written.append(p4)

    # 5. Ch 11–12: Internal vs External, Overflow & Countable Saturation
    p5 = DIAGRAMS_DIR / "ch11_internal_overflow.svg"
    p5.write_text(
        f"""<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 920 380">
  {SVG_SHARED_DEFS}
  <rect width="920" height="380" rx="20" fill="url(#bgCard)"/>
  <text x="36" y="42" fill="#f8fafc" font-family="system-ui, -apple-system, sans-serif" font-size="20" font-weight="700">Internal vs. External Entities — Overflow, Underflow &amp; ℵ₁-Saturation</text>
  <text x="36" y="66" fill="#94a3b8" font-family="system-ui, -apple-system, sans-serif" font-size="13">Because ℝ, ℕ, 𝕃, and 𝕀 have no least upper bounds in ℝ*, no internal set can stop cleanly at their boundary</text>

  <!-- Overflow / Underflow diagram -->
  <rect x="36" y="92" width="848" height="142" rx="16" fill="#0b1220" stroke="#334155"/>
  <text x="56" y="118" fill="#fbbf24" font-family="system-ui, sans-serif" font-size="12" font-weight="700">OVERFLOW ACROSS THE EXTERNAL GALAXY BOUNDARY ℕ ⊂ *ℕ</text>

  <!-- Finite segment N -->
  <rect x="64" y="142" width="330" height="44" rx="10" fill="#38bdf8" fill-opacity="0.14" stroke="#38bdf8" stroke-dasharray="5 3"/>
  <text x="229" y="169" text-anchor="middle" fill="#bae6fd" font-family="ui-monospace, monospace" font-size="13">External ℕ = &#123; 0, 1, 2, 3, … &#125; (no max!)</text>

  <!-- Fuzzy gap -->
  <line x1="414" y1="132" x2="414" y2="202" stroke="#f87171" stroke-width="2" stroke-dasharray="4 4"/>
  <text x="414" y="218" text-anchor="middle" fill="#fca5a5" font-family="system-ui, sans-serif" font-size="11" font-weight="700">External Cut (invisible to internal sets)</text>

  <!-- Infinite segment *N_inf -->
  <rect x="434" y="142" width="420" height="44" rx="10" fill="#10b981" fill-opacity="0.12" stroke="#34d399" stroke-dasharray="5 3"/>
  <text x="644" y="169" text-anchor="middle" fill="#a7f3d0" font-family="ui-monospace, monospace" font-size="13">External *ℕ_∞ = *ℕ \\ ℕ (no min!)</text>

  <!-- Internal set A spilling across -->
  <path d="M 64 136 L 566 136 L 566 192 L 64 192 Z" fill="none" stroke="#fbbf24" stroke-width="2.6"/>
  <circle cx="566" cy="164" r="6" fill="#fbbf24"/>
  <text x="566" y="126" text-anchor="middle" fill="#fde68a" font-family="ui-monospace, monospace" font-size="12" font-weight="700">Internal A ⊇ ℕ ⟹ ∃ K ∈ *ℕ_∞, &#123;0..K&#125; ⊆ A</text>

  <!-- Bottom 2 cards: Saturation & Hyperfinite Sets -->
  <rect x="36" y="250" width="414" height="104" rx="14" fill="#0b1220" stroke="#818cf8" stroke-opacity="0.6"/>
  <text x="56" y="276" fill="#a5b4fc" font-family="system-ui, sans-serif" font-size="12" font-weight="700">COUNTABLE SATURATION (CANTOR INTERSECTION)</text>
  <text x="56" y="302" fill="#e2e8f0" font-family="ui-monospace, monospace" font-size="13">A₀ ⊇ A₁ ⊇ A₂ ⊇ ⋯ (nonempty internal)</text>
  <text x="56" y="328" fill="#fbbf24" font-family="ui-monospace, monospace" font-size="13">⟹  ⋂_&#123;k ∈ ℕ&#125; A_k ≠ ∅  (diagonal witness!)</text>

  <rect x="470" y="250" width="414" height="104" rx="14" fill="#0b1220" stroke="#34d399" stroke-opacity="0.6"/>
  <text x="490" y="276" fill="#6ee7b7" font-family="system-ui, sans-serif" font-size="12" font-weight="700">HYPERFINITE SETS &amp; PIGEONHOLE PRINCIPLE</text>
  <text x="490" y="302" fill="#e2e8f0" font-family="ui-monospace, monospace" font-size="13">Internal bijection f : &#123;1..N&#125; ↔ A  (N ∈ *ℕ)</text>
  <text x="490" y="328" fill="#6ee7b7" font-family="ui-monospace, monospace" font-size="13">No internal proper subset of A embeds A!</text>
</svg>
""",
        encoding="utf-8",
    )
    written.append(p5)

    # 6. Ch 13–15: Zakon Superstructure & Enlargements
    p6 = DIAGRAMS_DIR / "ch13_superstructure_transfer.svg"
    p6.write_text(
        f"""<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 920 400">
  {SVG_SHARED_DEFS}
  <rect width="920" height="400" rx="20" fill="url(#bgCard)"/>
  <text x="36" y="42" fill="#f8fafc" font-family="system-ui, -apple-system, sans-serif" font-size="20" font-weight="700">Zakon Cumulative Superstructures V(X) &amp; Enlargement Transfer</text>
  <text x="36" y="66" fill="#94a3b8" font-family="system-ui, -apple-system, sans-serif" font-size="13">Every classical space, topology, measure, and operator lives at a finite rank V_n(X) and transfers via Δ₀ formulas</text>

  <!-- Left hierarchy V(X) -->
  <rect x="36" y="90" width="356" height="280" rx="16" fill="#0b1220" stroke="#334155"/>
  <text x="214" y="116" text-anchor="middle" fill="#fbbf24" font-family="system-ui, sans-serif" font-size="12" font-weight="700">STANDARD SUPERSTRUCTURE V(X)</text>
  <polygon points="214,344 86,144 342,144" fill="#fbbf24" fill-opacity="0.09" stroke="#fbbf24" stroke-width="1.8"/>
  <line x1="122" y1="200" x2="306" y2="200" stroke="#fbbf24" stroke-opacity="0.4" stroke-dasharray="4 3"/>
  <line x1="154" y1="252" x2="274" y2="252" stroke="#fbbf24" stroke-opacity="0.4" stroke-dasharray="4 3"/>
  <line x1="184" y1="298" x2="244" y2="298" stroke="#fbbf24" stroke-opacity="0.4" stroke-dasharray="4 3"/>
  <text x="214" y="176" text-anchor="middle" fill="#fde68a" font-family="ui-monospace, monospace" font-size="12">V₃(X) : topologies, measures, Duals</text>
  <text x="214" y="230" text-anchor="middle" fill="#fde68a" font-family="ui-monospace, monospace" font-size="12">V₂(X) : functions &amp; relations (Kuratowski)</text>
  <text x="214" y="278" text-anchor="middle" fill="#fde68a" font-family="ui-monospace, monospace" font-size="12">V₁(X) = X ∪ 𝒫(X)</text>
  <text x="214" y="324" text-anchor="middle" fill="#f8fafc" font-family="ui-monospace, monospace" font-size="12">V₀(X) = X (Individuals)</text>

  <!-- Transfer Bridge -->
  <path d="M 356 218 C 424 176, 480 176, 548 218" fill="none" stroke="#fbbf24" stroke-width="2.8" marker-end="url(#arrowGold)"/>
  <text x="452" y="176" text-anchor="middle" fill="#fde68a" font-family="ui-monospace, monospace" font-size="13" font-weight="700">*-Transform</text>
  <text x="452" y="194" text-anchor="middle" fill="#94a3b8" font-family="ui-monospace, monospace" font-size="11">φ ⟺ *φ (Δ₀)</text>

  <!-- Right hierarchy V(*X) -->
  <rect x="508" y="90" width="376" height="280" rx="16" fill="#0b1220" stroke="#334155"/>
  <text x="696" y="116" text-anchor="middle" fill="#7dd3fc" font-family="system-ui, sans-serif" font-size="12" font-weight="700">NONSTANDARD V(*X) — INTERNAL vs. EXTERNAL</text>
  <!-- Outer full cone V(*X) -->
  <polygon points="696,344 534,144 858,144" fill="#8b5cf6" fill-opacity="0.12" stroke="#a78bfa" stroke-dasharray="5 3"/>
  <!-- Inner internal cone *V(X) -->
  <polygon points="696,344 588,144 804,144" fill="#38bdf8" fill-opacity="0.16" stroke="#38bdf8" stroke-width="2"/>
  <text x="696" y="182" text-anchor="middle" fill="#bae6fd" font-family="ui-monospace, monospace" font-size="12" font-weight="700">Internal Universe ℐ = ⋃ *V_n(X)</text>
  <text x="696" y="206" text-anchor="middle" fill="#cbd5e1" font-family="system-ui, sans-serif" font-size="11">Closed under internal comprehension &amp; hyperfinite</text>
  <text x="696" y="224" text-anchor="middle" fill="#cbd5e1" font-family="system-ui, sans-serif" font-size="11">enlargement witnesses b ∈ ∩ &#123; *R(x) : x ∈ dom R &#125;</text>
  <text x="564" y="168" fill="#ddd6fe" font-family="ui-monospace, monospace" font-size="11">External</text>
  <text x="812" y="168" fill="#ddd6fe" font-family="ui-monospace, monospace" font-size="11">Loeb / ℝ</text>
  <text x="696" y="324" text-anchor="middle" fill="#7dd3fc" font-family="ui-monospace, monospace" font-size="12">*X (Enlarged Base)</text>
</svg>
""",
        encoding="utf-8",
    )
    written.append(p6)

    # 7. Ch 16: Loeb Measure Pipeline
    p7 = DIAGRAMS_DIR / "ch16_loeb_measure.svg"
    p7.write_text(
        f"""<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 920 330">
  {SVG_SHARED_DEFS}
  <rect width="920" height="330" rx="20" fill="url(#bgCard)"/>
  <text x="36" y="42" fill="#f8fafc" font-family="system-ui, -apple-system, sans-serif" font-size="20" font-weight="700">Peter Loeb's Theorem (1975) — From Hyperfinite Counting to Lebesgue Measure</text>
  <text x="36" y="66" fill="#94a3b8" font-family="system-ui, -apple-system, sans-serif" font-size="13">Countable saturation turns every finitely additive internal probability into a genuine σ-additive standard measure</text>

  <!-- 4 Pipeline Boxes -->
  <rect x="36" y="102" width="192" height="186" rx="14" fill="#0b1220" stroke="#38bdf8"/>
  <text x="132" y="130" text-anchor="middle" fill="#7dd3fc" font-family="system-ui, sans-serif" font-size="12" font-weight="700">1. HYPERFINITE GRID</text>
  <text x="132" y="164" text-anchor="middle" fill="#f8fafc" font-family="ui-monospace, monospace" font-size="13">Ω = &#123;0, 1/N, …, (N−1)/N&#125;</text>
  <text x="132" y="194" text-anchor="middle" fill="#cbd5e1" font-family="ui-monospace, monospace" font-size="12">Internal algebra 𝒜</text>
  <text x="132" y="220" text-anchor="middle" fill="#94a3b8" font-family="ui-monospace, monospace" font-size="12">ν(A) = |A| / N ∈ *ℝ</text>
  <text x="132" y="256" text-anchor="middle" fill="#38bdf8" font-family="system-ui, sans-serif" font-size="11">Uniform counting!</text>

  <line x1="232" y1="195" x2="256" y2="195" stroke="#fbbf24" stroke-width="2.4" marker-end="url(#arrowGold)"/>

  <rect x="262" y="102" width="192" height="186" rx="14" fill="#0b1220" stroke="#fbbf24"/>
  <text x="358" y="130" text-anchor="middle" fill="#fde68a" font-family="system-ui, sans-serif" font-size="12" font-weight="700">2. SHADOW PRE-MEASURE</text>
  <text x="358" y="164" text-anchor="middle" fill="#f8fafc" font-family="ui-monospace, monospace" font-size="14">μ₀(A) = sh(|A| / N)</text>
  <text x="358" y="194" text-anchor="middle" fill="#cbd5e1" font-family="system-ui, sans-serif" font-size="12">ℵ₁-Saturation collapses</text>
  <text x="358" y="214" text-anchor="middle" fill="#cbd5e1" font-family="system-ui, sans-serif" font-size="12">countable covers A ⊆ ⋃ A_k</text>
  <text x="358" y="256" text-anchor="middle" fill="#fbbf24" font-family="system-ui, sans-serif" font-size="11">Vacuously σ-additive on 𝒜!</text>

  <line x1="458" y1="195" x2="482" y2="195" stroke="#fbbf24" stroke-width="2.4" marker-end="url(#arrowGold)"/>

  <rect x="488" y="102" width="192" height="186" rx="14" fill="#0b1220" stroke="#a78bfa"/>
  <text x="584" y="130" text-anchor="middle" fill="#ddd6fe" font-family="system-ui, sans-serif" font-size="12" font-weight="700">3. LOEB σ-ALGEBRA L(𝒜)</text>
  <text x="584" y="164" text-anchor="middle" fill="#f8fafc" font-family="ui-monospace, monospace" font-size="13">Carathéodory Extension</text>
  <text x="584" y="194" text-anchor="middle" fill="#cbd5e1" font-family="ui-monospace, monospace" font-size="11">∀ ε&gt;0, ∃ A⊆B⊆C ∈ 𝒜,</text>
  <text x="584" y="214" text-anchor="middle" fill="#cbd5e1" font-family="ui-monospace, monospace" font-size="11">μ₀(C \\ A) &lt; ε</text>
  <text x="584" y="256" text-anchor="middle" fill="#c4b5fd" font-family="system-ui, sans-serif" font-size="11">Complete standard measure μ_L</text>

  <line x1="684" y1="195" x2="708" y2="195" stroke="#fbbf24" stroke-width="2.4" marker-end="url(#arrowGold)"/>

  <rect x="714" y="102" width="170" height="186" rx="14" fill="#0b1220" stroke="#34d399"/>
  <text x="799" y="130" text-anchor="middle" fill="#6ee7b7" font-family="system-ui, sans-serif" font-size="12" font-weight="700">4. LEBESGUE ON [0,1]</text>
  <text x="799" y="164" text-anchor="middle" fill="#f8fafc" font-family="ui-monospace, monospace" font-size="13">λ(E) = μ_L(st⁻¹(E))</text>
  <text x="799" y="196" text-anchor="middle" fill="#cbd5e1" font-family="ui-monospace, monospace" font-size="12">λ([a, b]) = b − a</text>
  <text x="799" y="220" text-anchor="middle" fill="#cbd5e1" font-family="ui-monospace, monospace" font-size="12">E Lebesgue ⟺</text>
  <text x="799" y="238" text-anchor="middle" fill="#6ee7b7" font-family="ui-monospace, monospace" font-size="12">st⁻¹(E) ∈ L(𝒜)</text>
</svg>
""",
        encoding="utf-8",
    )
    written.append(p7)

    # 8. Ch 17–19: Four Jewels of Part V
    p8 = DIAGRAMS_DIR / "ch17_19_applications_quartet.svg"
    p8.write_text(
        f"""<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 920 390">
  {SVG_SHARED_DEFS}
  <rect width="920" height="390" rx="20" fill="url(#bgCard)"/>
  <text x="36" y="42" fill="#f8fafc" font-family="system-ui, -apple-system, sans-serif" font-size="20" font-weight="700">Part V Panorama — Combinatorics, Completions &amp; Hyperfinite Approximation</text>
  <text x="36" y="66" fill="#94a3b8" font-family="system-ui, -apple-system, sans-serif" font-size="13">How enlargements unify Ramsey theory, Banach/p-adic completions, Stone duality, and Hahn–Banach</text>

  <!-- Panel 1: Ch 17 Ramsey -->
  <rect x="36" y="90" width="414" height="128" rx="14" fill="#0b1220" stroke="#f87171" stroke-opacity="0.6"/>
  <text x="56" y="116" fill="#fca5a5" font-family="system-ui, sans-serif" font-size="12" font-weight="700">CH. 17 · ULTRAFILTER RAMSEY &amp; PARIS–HARRINGTON</text>
  <text x="56" y="144" fill="#e2e8f0" font-family="ui-monospace, monospace" font-size="12">Nonstandard witness ω ∈ *ℕ colors pairs (n, ω)</text>
  <text x="56" y="168" fill="#cbd5e1" font-family="system-ui, sans-serif" font-size="12">Steps: Infinite Ramsey ⟹ Compactness Transfer ⟹</text>
  <text x="56" y="190" fill="#fde68a" font-family="ui-monospace, monospace" font-size="12">Finite Ramsey &amp; Large-Set Paris–Harrington (|H| &gt; min H)</text>

  <!-- Panel 2: Ch 18 Nonstandard Hulls & p-adics -->
  <rect x="470" y="90" width="414" height="128" rx="14" fill="#0b1220" stroke="#38bdf8" stroke-opacity="0.6"/>
  <text x="490" y="116" fill="#7dd3fc" font-family="system-ui, sans-serif" font-size="12" font-weight="700">CH. 18 · COMPLETION BY ENLARGEMENT</text>
  <text x="490" y="144" fill="#e2e8f0" font-family="ui-monospace, monospace" font-size="12">M̂ = M_fin / ≈  (Banach &amp; Metric Nonstandard Hulls)</text>
  <text x="490" y="168" fill="#cbd5e1" font-family="system-ui, sans-serif" font-size="12">Same quotient builds ℤ_p = *ℤ / ⋂ p^n *ℤ, ℚ_p = *ℚ_fin / 𝕀_p,</text>
  <text x="490" y="190" fill="#bae6fd" font-family="ui-monospace, monospace" font-size="12">and formal power series R⟦X⟧ from hyperpolynomials!</text>

  <!-- Panel 3: Ch 19 Graph Coloring & Boolean Algebras -->
  <rect x="36" y="236" width="414" height="128" rx="14" fill="#0b1220" stroke="#34d399" stroke-opacity="0.6"/>
  <text x="56" y="262" fill="#6ee7b7" font-family="system-ui, sans-serif" font-size="12" font-weight="700">CH. 19A · DE BRUIJN–ERDŐS &amp; STONE DUALITY</text>
  <text x="56" y="290" fill="#e2e8f0" font-family="ui-monospace, monospace" font-size="12">Every finite H ⊆ G k-colorable ⟹ hyperfinite G⁺ k-colorable</text>
  <text x="56" y="314" fill="#cbd5e1" font-family="system-ui, sans-serif" font-size="12">Every Boolean algebra B embeds into hyperfinite B⁺ = *𝒫(F₀),</text>
  <text x="56" y="336" fill="#6ee7b7" font-family="ui-monospace, monospace" font-size="12">whose internal atoms yield Stone's Representation Theorem!</text>

  <!-- Panel 4: Ch 19 Hahn-Banach -->
  <rect x="470" y="236" width="414" height="128" rx="14" fill="#0b1220" stroke="#fbbf24" stroke-opacity="0.65"/>
  <text x="490" y="262" fill="#fde68a" font-family="system-ui, sans-serif" font-size="12" font-weight="700">CH. 19B · HYPERFINITE HAHN–BANACH EXTENSION</text>
  <text x="490" y="290" fill="#e2e8f0" font-family="ui-monospace, monospace" font-size="12">Finite-dim induction transfers to hyperfinite span V⁺ ⊇ V</text>
  <text x="490" y="314" fill="#cbd5e1" font-family="system-ui, sans-serif" font-size="12">Extend *f : *U ∩ V⁺ → *ℝ dominated by *p, then take shadow:</text>
  <text x="490" y="336" fill="#fbbf24" font-family="ui-monospace, monospace" font-size="12">F(v) := sh( Φ(v) )  gives exact global functional on V!</text>
</svg>
""",
        encoding="utf-8",
    )
    written.append(p8)

    return written


def main() -> None:
    MODELS_DIR.mkdir(parents=True, exist_ok=True)
    builders = [
        build_hyperreal_telescope(),
        build_ultrapower_germs(),
        build_hyperfinite_riemann_loeb(),
        build_superstructure_cone(),
        build_padic_stone_hull(),
    ]
    for b in builders:
        usdz, glb = b.export_glb_and_usdz(MODELS_DIR)
        print(
            f"[3D OK] {b.name}: {usdz.name} ({usdz.stat().st_size // 1024} KB, ARKit/visionOS strict-valid) "
            f"+ {glb.name} ({glb.stat().st_size // 1024} KB)"
        )

    svgs = write_svgs()
    print(f"[SVG OK] Wrote {len(svgs)} bespoke SVG diagrams to {STATIC_DIR}")


if __name__ == "__main__":
    main()
