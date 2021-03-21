; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
 (make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s

(defdata data (listof atom))

(defdata sender-state (record (to-send . data)))


;; (defthm ss-make
;;   (implies (datap data)
;; 	   (sender-statep (sender-state data))))

(defdata receiver-state (record (received . data)))

;; (defdata sender-out (record (new-state . sender-state)
;; 			    (packet . atom)))

(defdata sender-out (cons sender-state atom))

(set-ignore-ok t)

(definec sender (sender-state :sender-state) :sender-out
  ;; (sender-out sender-state 1 ;; (car (sender-state-to-send sender-state))
  ;; 	      )
  (cons
   (set-sender-state-to-send (cdr (sender-state-to-send sender-state)) sender-state)
   (car (sender-state-to-send sender-state))
   ))


(definec receiver (receiver-state :receiver-state packet :atom) :receiver-state
  (set-receiver-state-received (app (receiver-state-received receiver-state) (list packet)) receiver-state))


(definec simulator (ss :sender-state rs :receiver-state cd :nat) :data
  (cond
   ((zp cd) (receiver-state-received rs))
   (T (let* ((ss-out (sender ss))
	     (new-ss (car ss-out))
	     (packet (cdr ss-out))
	     (new-rs (receiver rs packet)))
	(simulator new-ss new-rs (1- cd))))))

(definec simulator* (data :data) :data
  :body-contracts-strictp nil
  (simulator (sender-state data) (receiver-state '()) (len data)))

(definec f (data :data) :data
  (if (lendp data)
      data
    (cons (car data) (f (cdr data)))))

(defthm foothm
  (implies (and (datap l))
	   (equal (f l) l)))

(defthm receiver-cons
  (implies (and (datap l)
		(atom p))
	   (equal (receiver-state-received (receiver (receiver-state l) p)) (app l (list p)))))

(defthm f-sim-relation
  (implies (and (datap in)
		(datap out))
	   (equal (simulator (sender-state in) (receiver-state out) (len in)) (app out (f in))))
  :hints (("Goal" :induct (app out (f in)))))

(test?
  (implies (and (datap in)
		(datap out))
	   (equal (simulator (sender-state in) (receiver-state out) (len in)) (app out (f in)))))

(thm (implies (and (datap data))
	      (equal (f data) (simulator* data))))

(thm (implies (and (datap data))
	      (equal data (simulator* data))))

