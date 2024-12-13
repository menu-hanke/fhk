local({
anchor <- new.env(hash=TRUE, parent=emptyenv())
function(fname, expr) {
	if (!is.null(fname)) {
		if (is.null(anchor[[fname]])) {
			anchor[[fname]] <- TRUE
			source(fname)
		}
	}
	fun <- eval(parse(text=expr))
	# must be anchored here because rust code doesn't anchor this.
	anchor[[expr]] <- fun
	fun
}
})
