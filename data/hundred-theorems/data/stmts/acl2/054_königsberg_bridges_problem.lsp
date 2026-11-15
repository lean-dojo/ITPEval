;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__054, "Königsberg Bridges Problem": no ordering and
;; orientation of the seven fixed undirected bridges forms a contiguous trail
;; that uses every bridge exactly once. This file contains no proof.

(in-package "ACL2")

(defun ht054-edge-recordp (edge)
  (and (true-listp edge)
       (equal (len edge) 2)
       (natp (nth 0 edge))
       (natp (nth 1 edge))))

(defun ht054-edge-listp (edges)
  (if (consp edges)
      (and (ht054-edge-recordp (car edges))
           (ht054-edge-listp (cdr edges)))
    (equal edges nil)))

(defun ht054-contiguous-path-p (path)
  (if (and (consp path)
           (consp (cdr path)))
      (and (equal (nth 1 (car path))
                  (nth 0 (cadr path)))
           (ht054-contiguous-path-p (cdr path)))
    t))

(defun ht054-path-p (path)
  (and (true-listp path)
       (ht054-edge-listp path)
       (ht054-contiguous-path-p path)))

(defun ht054-normalize-edge (edge)
  (let ((left (nth 0 edge))
        (right (nth 1 edge)))
    (if (<= left right)
        (list left right)
      (list right left))))

(defun ht054-normalize-edges (edges)
  (if (consp edges)
      (cons (ht054-normalize-edge (car edges))
            (ht054-normalize-edges (cdr edges)))
    nil))

(defun ht054-remove-first-equal (item items)
  (if (consp items)
      (if (equal item (car items))
          (cdr items)
        (cons (car items)
              (ht054-remove-first-equal item (cdr items))))
    nil))

(defun ht054-multiset-equal-p (left right)
  (if (consp left)
      (and (member-equal (car left) right)
           (ht054-multiset-equal-p
            (cdr left)
            (ht054-remove-first-equal (car left) right)))
    (equal right nil)))

(defun ht054-eulerian-path-p (path)
  (ht054-multiset-equal-p
   (list (list 0 1)
         (list 0 2)
         (list 0 3)
         (list 1 2)
         (list 1 2)
         (list 2 3)
         (list 2 3))
   (ht054-normalize-edges path)))

(defun hundred-theorems-054-konigsberg-bridges-problem-statement (path)
  (implies
   (ht054-path-p path)
   (not (ht054-eulerian-path-p path))))

(value-triple :itpeval-statement-checked)
:q
