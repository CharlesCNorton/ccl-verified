# Formally Verified Connected Component Labeling in Coq

A complete formal verification of the Connected Component Labeling (CCL) algorithm - a fundamental computer vision algorithm used in medical imaging, industrial inspection, and image analysis.

## 🎯 What is this?

This repository contains an 8,000+ line Coq proof that Connected Component Labeling is mathematically correct. CCL identifies and labels connected regions in binary images - critical for applications like:
- Medical image analysis (tumor detection, cell counting)
- Industrial quality control (defect detection)
- Document processing (character segmentation)
- Robotics (object recognition)

## ✨ Key Achievements

- **Zero admits or axioms** - Complete mechanical proof
- **Handles arbitrary image sizes** - No fixed dimension limitations  
- **Proven correctness properties**:
  - Background pixels receive label 0
  - Foreground pixels receive positive labels
  - Connected pixels receive identical labels
  - Labels form proper equivalence classes
- **Efficient union-find implementation** with proven invariants
- **Executable** - Can run on actual images and verify results

## 🚀 Quick Start

```coq
(* Load the verification *)
Require Import CCL-verified.

(* Define a simple 3x3 image *)
Definition my_image := mkImage 3 3 (fun c =>
  match c with
  | (0,0) | (1,0) | (0,1) => true  (* L-shaped component *)
  | (2,2) => true                   (* Isolated pixel *)
  | _ => false
  end).

(* Run the verified algorithm *)
Compute ccl_4 my_image.
(* Returns: (0,0)→1, (1,0)→1, (0,1)→1, (2,2)→2 *)
```

## 📊 Example Verification

The code includes extensive test cases demonstrating correctness:

```coq
(* Proves adjacent pixels get same label *)
Theorem adjacent_pixels_same_label : ∀ img c1 c2,
  get_pixel img c1 = true →
  get_pixel img c2 = true →
  adjacent_4 c1 c2 = true →
  ccl_4 img c1 = ccl_4 img c2.
```

## 🔬 Technical Details

- **Algorithm**: Single-pass CCL with union-find
- **Connectivity**: 4-connectivity (8-connectivity framework included)
- **Proof approach**: Inductive invariants through fold_left
- **Key innovation**: Dual invariant preservation for label bounds

## 📁 Repository Structure

- `CCL-verified.v` - Complete formalization and proofs
- Example images and test cases included
- Visualization functions for debugging

## 🏗️ Building

```bash
coqc CCL-verified.v
```

Requires: Coq 8.13 or later

## 🤝 Contributing

Future work includes:
- Completeness proof (same label implies connected)
- 8-connectivity verification
- Performance optimizations
- Integration with real image processing pipelines

## 📄 License

[Your chosen license]

## 📚 Citation

If you use this verification in your research, please cite:
```
@software{norton2024ccl,
  author       = {Norton, Charles C.},
  title        = {Formally Verified Connected Component Labeling in {Coq}},
  year         = {2025},
  publisher    = {GitHub},
  url          = {https://github.com/CharlesCNorton/ccl-verified},
  note         = {8,000+ line formal verification with zero admits or axioms}
}

@inproceedings{norton2024first,
  author       = {Norton, Charles C.},
  title        = {The First Formally Verified Computer Vision Algorithm: 
                   A Complete Proof of Connected Component Labeling in {Coq}},
  year         = {2024},
  note         = {Manuscript submitted for publication}
}
```

## 🎓 Significance

To our knowledge, this represents the first complete formal verification of the Connected Component Labeling algorithm, providing mathematical certainty for a critical computer vision primitive used in safety-critical applications.
