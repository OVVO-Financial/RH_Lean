# Original user-supplied R visualization, 2026-10-11.
# This is a schematic additive prime-period superposition, NOT the Euler
# Mobius field or Perron's logarithmic-frequency expansion.
library(ggplot2)
library(tidyr)

x_val <- 30

get_primes <- function(n) {
  if (n < 2) return(numeric(0))
  p <- 2:n
  primes <- c()
  while (length(p) > 0) {
    prime <- p[1]
    primes <- c(primes, prime)
    p <- p[p %% prime != 0]
  }
  return(primes)
}

primes <- get_primes(x_val)
t <- seq(0, x_val, length.out = 15000)
wave_data <- data.frame(t = t)
for (p in primes) {
  wave_data[[paste0("p=", p)]] <- ifelse(
    t >= p, sin(2 * pi * (1/p) * t), 0
  )
}
wave_data$Superposition <- rowSums(wave_data[, -1])
wave_long <- pivot_longer(
  wave_data, cols = -t, names_to = "Wave", values_to = "Amplitude"
)
prime_waves <- wave_long[wave_long$Wave != "Superposition", ]
super_wave <- wave_long[wave_long$Wave == "Superposition", ]

ggplot() +
  geom_line(data = prime_waves, aes(x = t, y = Amplitude, color = Wave),
            linewidth = 0.5, alpha = 0.8) +
  geom_line(data = super_wave, aes(x = t, y = Amplitude),
            color = "white", linewidth = 1.2, alpha = 0.9) +
  scale_color_viridis_d(option = "turbo") +
  theme_dark() +
  labs(
    title = paste("Staggered Prime Number Superposition (x =", x_val, ")"),
    subtitle = "Resultant Wave: Y(t) = Σ sin(2πt/p) for t ≥ p",
    x = "Time (t)", y = "Amplitude", color = "Primes\n(Period = p)"
  ) +
  theme(
    plot.title = element_text(color = "white", size = 14, face = "bold"),
    plot.subtitle = element_text(color = "lightgrey", size = 12),
    plot.background = element_rect(fill = "#1e212b", color = NA),
    panel.background = element_rect(fill = "#252936", color = NA),
    panel.grid.major = element_line(color = "#3a4053", linewidth = 0.5),
    panel.grid.minor = element_blank(),
    axis.text = element_text(color = "lightgrey"),
    axis.title = element_text(color = "white"),
    legend.background = element_rect(fill = "#1e212b"),
    legend.text = element_text(color = "lightgrey"),
    legend.title = element_text(color = "white")
  )
