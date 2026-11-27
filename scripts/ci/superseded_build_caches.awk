# Input: newest-first created_at, id and key for one ref, separated by tabs.
# Keep the verified full key, newer caches, and every entry when the full key is absent.
BEGIN { FS = "\t" }
$3 == current && current != "" { verified_at = $1; next }
verified_at != "" && $1 < verified_at { print }
