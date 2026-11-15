;; Statement-only formalization of thousand-theorems corpus artifact Q8066795,
;; "Zariski's main theorem": a proper morphism of schemes with finite fiber
;; over a point is finite over some open neighborhood of that point.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The geometry argument indexes an arbitrary universe of schemes. Predicates
;; represent the full, potentially infinite point and open-set carriers; no
;; carrier is enumerated or bounded. The coherence conditions below are the
;; many-sorted ACL2 presentation of scheme morphisms and base restriction.

(defstub q8066795-scheme-p (geometry scheme) t)
(defstub q8066795-point-p (geometry scheme point) t)
(defstub q8066795-open-p (geometry scheme open) t)
(defstub q8066795-open-member-p
  (geometry scheme open point)
  t)

(defstub q8066795-morphism-p
  (geometry source target morphism)
  t)
(defstub q8066795-morphism-apply
  (geometry source target morphism point)
  t)

(defstub q8066795-open-subscheme
  (geometry scheme open)
  t)
(defstub q8066795-preimage-open-subscheme
  (geometry source target morphism open)
  t)
(defstub q8066795-morphism-restrict
  (geometry source target morphism open)
  t)

;; These are the source predicates IsProper and IsFinite on scheme morphisms.
;; They are indexed by the complete typed morphism data, rather than being
;; untyped labels attached to an ACL2 object.

(defstub q8066795-proper-morphism-p
  (geometry source target morphism)
  t)
(defstub q8066795-finite-morphism-p
  (geometry source target morphism)
  t)

(defun-sk q8066795-point-and-open-typing-p (geometry)
  (forall (scheme open point)
    (and
     (implies
      (q8066795-point-p geometry scheme point)
      (q8066795-scheme-p geometry scheme))
     (implies
      (q8066795-open-p geometry scheme open)
      (q8066795-scheme-p geometry scheme))
     (implies
      (q8066795-open-member-p geometry scheme open point)
      (and
       (q8066795-open-p geometry scheme open)
       (q8066795-point-p geometry scheme point))))))

(defun-sk q8066795-morphism-typing-p (geometry)
  (forall (source target morphism point)
    (and
     (implies
      (q8066795-morphism-p geometry source target morphism)
      (and
       (q8066795-scheme-p geometry source)
       (q8066795-scheme-p geometry target)))
     (implies
      (and
       (q8066795-morphism-p geometry source target morphism)
       (q8066795-point-p geometry source point))
      (q8066795-point-p
       geometry
       target
       (q8066795-morphism-apply
        geometry source target morphism point))))))

(defun-sk q8066795-open-subscheme-coherence-p (geometry)
  (forall (scheme open point)
    (implies
     (q8066795-open-p geometry scheme open)
     (and
      (q8066795-scheme-p
       geometry
       (q8066795-open-subscheme geometry scheme open))
      (equal
       (if
        (q8066795-point-p
         geometry
         (q8066795-open-subscheme geometry scheme open)
         point)
        t
        nil)
       (if
        (and
         (q8066795-point-p geometry scheme point)
         (q8066795-open-member-p
          geometry scheme open point))
        t
        nil))))))

(defun-sk q8066795-preimage-subscheme-coherence-p (geometry)
  (forall (source target morphism open point)
    (implies
     (and
      (q8066795-morphism-p geometry source target morphism)
      (q8066795-open-p geometry target open))
     (and
      (q8066795-scheme-p
       geometry
       (q8066795-preimage-open-subscheme
        geometry source target morphism open))
      (equal
       (if
        (q8066795-point-p
         geometry
         (q8066795-preimage-open-subscheme
          geometry source target morphism open)
         point)
        t
        nil)
       (if
        (and
         (q8066795-point-p geometry source point)
         (q8066795-open-member-p
          geometry
          target
          open
          (q8066795-morphism-apply
           geometry source target morphism point)))
        t
        nil))))))

(defun-sk q8066795-restriction-coherence-p (geometry)
  (forall (source target morphism open point)
    (implies
     (and
      (q8066795-morphism-p geometry source target morphism)
      (q8066795-open-p geometry target open))
     (and
      (q8066795-morphism-p
       geometry
       (q8066795-preimage-open-subscheme
        geometry source target morphism open)
       (q8066795-open-subscheme geometry target open)
       (q8066795-morphism-restrict
        geometry source target morphism open))
      (implies
       (q8066795-point-p
        geometry
        (q8066795-preimage-open-subscheme
         geometry source target morphism open)
        point)
       (equal
        (q8066795-morphism-apply
         geometry
         (q8066795-preimage-open-subscheme
          geometry source target morphism open)
         (q8066795-open-subscheme geometry target open)
         (q8066795-morphism-restrict
          geometry source target morphism open)
         point)
        (q8066795-morphism-apply
         geometry source target morphism point)))))))

(defun-sk q8066795-morphism-property-typing-p (geometry)
  (forall (source target morphism)
    (and
     (implies
      (q8066795-proper-morphism-p
       geometry source target morphism)
      (q8066795-morphism-p geometry source target morphism))
     (implies
      (q8066795-finite-morphism-p
       geometry source target morphism)
      (q8066795-morphism-p geometry source target morphism)))))

(defun q8066795-scheme-geometry-p (geometry)
  (and
   (q8066795-point-and-open-typing-p geometry)
   (q8066795-morphism-typing-p geometry)
   (q8066795-open-subscheme-coherence-p geometry)
   (q8066795-preimage-subscheme-coherence-p geometry)
   (q8066795-restriction-coherence-p geometry)
   (q8066795-morphism-property-typing-p geometry)))

;; Set.Finite for the fiber f ⁻¹' {y} is represented exactly by a finite
;; duplicate-free list whose membership is equivalent, for every ACL2 object,
;; to being a source point mapped to y. The list is only an internal witness.

(defun q8066795-list-member-p (value values)
  (if (consp values)
      (or (equal value (car values))
          (q8066795-list-member-p value (cdr values)))
    nil))

(defun q8066795-no-duplicates-p (values)
  (if (consp values)
      (and
       (not
        (q8066795-list-member-p (car values) (cdr values)))
       (q8066795-no-duplicates-p (cdr values)))
    (equal values nil)))

(defun-sk q8066795-fiber-enumeration-p
    (geometry source target morphism point enumeration)
  (forall (source-point)
    (equal
     (if
      (and
       (q8066795-point-p geometry source source-point)
       (equal
        (q8066795-morphism-apply
         geometry source target morphism source-point)
        point))
      t
      nil)
     (if
      (q8066795-list-member-p source-point enumeration)
      t
      nil))))

(defun-sk q8066795-finite-fiber-p
    (geometry source target morphism point)
  (exists (enumeration)
    (and
     (true-listp enumeration)
     (q8066795-no-duplicates-p enumeration)
     (q8066795-fiber-enumeration-p
      geometry source target morphism point enumeration))))

(defun q8066795-finite-restriction-witness-p
    (geometry source target morphism point open)
  (and
   (q8066795-open-p geometry target open)
   (q8066795-open-member-p geometry target open point)
   (q8066795-finite-morphism-p
    geometry
    (q8066795-preimage-open-subscheme
     geometry source target morphism open)
    (q8066795-open-subscheme geometry target open)
    (q8066795-morphism-restrict
     geometry source target morphism open))))

(defun-sk q8066795-finite-restriction-exists-p
    (geometry source target morphism point)
  (exists (open)
    (q8066795-finite-restriction-witness-p
     geometry source target morphism point open)))

(defun-sk
    thousand-theorems-q8066795-zariski-s-main-theorem-statement
    ()
  (forall (geometry source target morphism point)
    (implies
     (and
      (q8066795-scheme-geometry-p geometry)
      (q8066795-scheme-p geometry source)
      (q8066795-scheme-p geometry target)
      (q8066795-morphism-p geometry source target morphism)
      (q8066795-point-p geometry target point)
      (q8066795-proper-morphism-p
       geometry source target morphism)
      (q8066795-finite-fiber-p
       geometry source target morphism point))
     (q8066795-finite-restriction-exists-p
      geometry source target morphism point))))

(value-triple :itpeval-statement-checked)
:q
