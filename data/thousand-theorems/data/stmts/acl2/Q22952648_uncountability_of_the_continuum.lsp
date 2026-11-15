;; Statement-only formalization of Thousand Theorems artifact Q22952648
;; (thousand-theorems__acl2__Q22952648), "Uncountability of the continuum":
;; using the standard equinumerosity of the reals with infinite Boolean
;; sequences, every natural-number enumeration misses its complemented
;; diagonal sequence. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; This conservative interface is an arbitrary proposed enumeration: row N is
;; the Boolean sequence whose value at column K is Q22952648-ENUMERATED-BIT.

(defstub q22952648-enumerated-bit (row column) t)

(defun q22952648-bit (row column)
  (if (q22952648-enumerated-bit row column)
      t
    nil))

(defun q22952648-diagonal-bit (column)
  (if (q22952648-bit column column)
      nil
    t))

(defun-sk q22952648-row-equals-diagonal-p (row)
  (forall (column)
    (implies
     (natp column)
     (equal
      (q22952648-bit row column)
      (q22952648-diagonal-bit column)))))

(defun-sk thousand-theorems-q22952648-uncountability-statement ()
  (forall (row)
    (implies
     (natp row)
     (not (q22952648-row-equals-diagonal-p row)))))

(value-triple :itpeval-statement-checked)
:q
