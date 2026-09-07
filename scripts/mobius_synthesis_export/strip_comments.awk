BEGIN { depth = 0 }
{
  line = $0; out = ""; i = 1
  while (i <= length(line)) {
    two = substr(line, i, 2)
    if (depth > 0) {
      if (two == "/-") { depth++; i += 2 }
      else if (two == "-/") { depth--; i += 2 }
      else { i++ }
    } else {
      if (two == "/-") { depth++; i += 2 }
      else if (two == "--") { break }
      else { out = out substr(line, i, 1); i++ }
    }
  }
  print out
}
